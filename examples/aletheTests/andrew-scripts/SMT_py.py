###################################
#
#	Library for SMT debugging with COQ
#	LMF, CNRS & Universite Paris-Saclay
#
#   Copyright 2022-2023
#	Author: Andrei Samokish
#
###################################

import os
import ds_interact as DSI
import time
import re

class coqSMTworker:
    # outputFile deprecated
    def __init__(self, outputFolder, tryFile, smtFile, stopOnProblem = True):
        self.outputFolder = outputFolder
        self.resFileName = tryFile
        self.reportFile = None
        self.smtFile = smtFile
        self.stopOnProblem = stopOnProblem

    # creates Coq file for execution, starts debugging
    def run(self):
        t1 = time.time()

        smtOutFile = self.resFileName  +'_' + self.smtFile + '.v'
        print ('smtOutFile', smtOutFile)
        if os.path.isfile(os.path.join(self.outputFolder, smtOutFile)):
            print ('debugging file already exists, aborting')
            return -1
        with open(os.path.join(self.outputFolder, 'report.txt'), 'w') as self.reportFile:
            with open(os.path.join(self.outputFolder, smtOutFile), 'w') as self.provFile:
                self.start()
                self.provFile.write('\n(** studying ' + self.smtFile  + ' **)')
                self.command('Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.')
                self.command('From SMTCoq Require Import SMTCoq.')
                self.command('Require Import Bool PArray Int63 List ZArith.')

                self.command('Local Open Scope int63_scope.')
                self.command('Open Scope Z_scope.')
                self.command('Set Printing Depth 250.')

                self.command('Module ' + self.smtFile  + '.')
                self.command('Section ' + self.smtFile  + '.')

                #execStr="Parse_certif_verit t_i t_func t_atom t_form root used_roots trace \"%s.smt2\" \"%s.vtlog\"."%(self.smtFile , self.smtFile )
                execStr = "Parse_certif_verit t_i t_func t_atom t_form root used_roots trace \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/andrew-scripts/%s.smt2\" \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/andrew-scripts/%s.pf\"." % (
                self.smtFile, self.smtFile)

                out, err =self.command(execStr)
                self.command("Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.")
                self.command("Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).")
                self.command("Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.")
                time.sleep(4)
                out, err = self.command("Print trace.")
                self.provFile.write('\n(*' + out + '*)')

                self.performStudy(out)

                self.terminate()

        print ('FIN', time.time() - t1, smtOutFile)
        return 0

    #extracts the expected number of strings, and performs debug step by step
    def performStudy(self, textOriginal):
        text = textOriginal[textOriginal.find('(', textOriginal.find('t_form') ):]
        self.command("Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).")
        sCounter = 0
        for line in traceLineReader(text):
            sCounter += 1

            #self.command('Set Printing All.')
            execStr = " Definition s%d := Eval compute in step_checker s%d (%s)"%(sCounter, sCounter-1, line)
            self.command(execStr)
            out, err = self.command("Print s%d"%sCounter)
            self.provFile.write('\n(*' + cleanOutput(out) + '*)')

            # performs studying till founds the '0%int63' in output
            if ':: 0%int63 ' in out:
                self.provFile.write('\n(* ====> ":: 0%int63 " in output found, break *)')
                self.command("Definition confl := Eval compute in let (_, _, confl) := trace in confl.")
                self.command("Compute (C.is_false (S.get s%d confl))."%sCounter)
                if self.stopOnProblem:
                    break

    def start(self):
        self.process = DSI.InteractiveProcess('coqtop', cwd=self.outputFolder)
        time.sleep(1)
        print ("START:", self.process.read())

        return

    def command(self, message, pollInterval=0.5):  # 0.1 is too small when excel used
        originalMessage = message
        if not message.strip():
            return '',''
        if  message.strip() == '.':
            return '', ''

        if not message.strip().endswith('.'):
            message += '.'

        if message.strip() == '.':
            return '', ''
        if message.strip().startswith('.'):
            message = message.replace('.', ' ', 1)

        message.replace('..', '.')
        if self.provFile:
            self.provFile.write('\n' + message)
            self.provFile.flush()

        self.reportFile.write('\n::::message::::\n' + message)
        stdout, stderr = self.process.interact(message + " \n", pollInterval)
        if 'Require Import' in message:
            # importing is slow, interaction can miss output
            time.sleep(3)
            tempOout, tempErr = self.process.interact("Print Libraries. \n", pollInterval)
            pass

        if False:
            if stdout:
                print ('stdout', stdout)
            if stderr and len(stderr) > 20:
                print ('stderr', stderr)

        if stderr and '^^^' in stderr and 'Error:' in stderr:
            self.reportFile.write('::::stderr:::::\n' + stderr)
            print ('message >>', originalMessage)
            print ('err!', stderr)
            #print (x)


        return stdout, stderr

    def terminate(self):
        self.process.process.kill()
        pass

# separates by logic
# skip last line!
def traceLineReader(data):
    # proposal: skip ( ), return data after '::'
    pairArr = [data[0] , ' ']
    braketCounter = 0

    currClearText = ''
    dataLen = len(data)

    for i in range(1, dataLen):
        pairArr[1] = data[i]
        pair = pairArr[0] + pairArr[1]
        if data[i] == '(':
            braketCounter += 1

        if data[i] == ')':
            braketCounter -= 1

        currClearText += data[i]

        if not braketCounter:
            if pair == '::':
                if currClearText.strip() and len(currClearText.strip()) > 2:
                    yield currClearText[:(len(currClearText)-2)].strip()
                currClearText = ''
        pairArr[0] = data[i]

    # skip the last line!
    #yield currClearText

test = """
s1 = 
({|
   PArray.Map.this :=
     PArray.Map.Raw.Node (PArray.Map.Raw.Leaf (list int)) 0%int63 
       (5%int63 :: nil)
       (PArray.Map.Raw.Node (PArray.Map.Raw.Leaf (list int)) 1%int63 
          (10%int63 :: nil)
          (PArray.Map.Raw.Node (PArray.Map.Raw.Leaf (list int)) 2%int63
             (9%int63 :: 13%int63 :: 14%int63 :: nil) (PArray.Map.Raw.Leaf (list int))
             1) 2) 3;
   PArray.Map.is_bst := ...)
     : PArray.Map.bst (list int) * list int * int"""
# separate function clearing text with regular expression
# replaces ' 4)' -> ')' and  ' 3;' -> ';'
def removeLeafNumbers(text):
    pattern = r'\s+\d+\)'
    cleared = re.sub(pattern, ')', text)
    pattern = r'\s+\d+\;'
    cleared = re.sub(pattern, ';', cleared)
    return cleared

# function to clean up debugging text
def cleanOutput(text):
    res =  text[:text.find('PArray.Map.is_bst')]

    # replaces ' 4)' -> ')' and  ' 3;' -> ';'
    res = removeLeafNumbers(res)
    # remove number type
    res = res.replace('%int63', '')
    # study arrays, replace brackets
    pos = res.find('::')
    while pos != -1:
        leftBrace = res.rfind('(', 0, pos)
        rightBrace = res.find(')', pos)
        res = rpcSInd(res, '[', leftBrace)
        res = rpcSInd(res, ']', rightBrace)

        pos = res.find('::', rightBrace)

    res = res.replace(' :: nil', '')
    res = res.replace('::', ',')

    res = res.replace('(list int)', '')
    res = res.replace('(PArray.Map.Raw.Leaf )', '')
    res = res.replace('PArray.Map.Raw.Node ', '')
    res = res.replace('\n', ' ')
    pos = res.find('  ')
    while pos != -1:
        res = res.replace('  ', ' ')
        pos = res.find('  ')

    return res

# replace given letter at the given index
def rpcSInd(text, letter, index):
    res = text[:index] + letter + text[index+1:]
    return res
#print (cleanOutput(test))

# exec the debugger
def runDebug(src=r'/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/andrew-scripts/', tryFile = 'test7'):
    coqFileReader = coqSMTworker(outputFolder=r'/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/andrew-scripts',
                                 tryFile='debug',
                                 smtFile='test7')

    coqFileReader.run()

runDebug()

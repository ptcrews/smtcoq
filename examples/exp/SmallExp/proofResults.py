#Take an op.txt file and return a csv classifying the results
#!/usr/bin/python3
import re
from enum import Enum

def updateRes(ind, o):
  if o == 1:
    op1[ind] += 1
  elif o == 2:
    op2[ind] += 1
  elif o == 3:
    op3[ind] += 1
  elif o == 4:
    op4[ind] += 1
  elif o == 5:
    op5[ind] += 1
  elif o == 6:
    op6[ind] += 1
  elif o == 7:
    op7[ind] += 1
  elif o == 8:
    op8[ind] += 1
  elif o == 9:
    op9[ind] += 1
  elif o == 10:
    op10[ind] += 1
  elif o == 11:
    op11[ind] += 1
  elif o == 12:
    op12[ind] += 1

def writeCSV(l,f):
  line = ""
  for i in l:
    line += (str(i) + ",")
  line += "\n"
  f.write(line)

fipname = "ZorderAllOp.txt" #input('Enter file (with relative path) to search: ')
f1 = open(fipname, "r")
f1lines = f1.readlines()
print("Total number of lines in input file is " + str(len(f1lines)))

fabdopname = "ZorderAllAbds.csv" #input('Enter file name for abducts output: ')
f2 = open(fabdopname, "w")
f2.write("Goal, Abducts 1, Abducts 2, Abducts 3, Abducts 4, Abducts 5, Abducts 6, Abducts 7, Abducts 8, Abducts 9, Abducts 10, Abducts 11, Abducts 12 \n")
#number of goals in the file
numgoals = 0
#for each config, [# get-abd successes, # smt successes, # non-bool equality failures, # abd reconstructr failures, # atom unexp type failure, # non-linear failure]
op1 = [0, 0, 0, 0, 0, 0]
op2 = [0, 0, 0, 0, 0, 0]
op3 = [0, 0, 0, 0, 0, 0]
op4 = [0, 0, 0, 0, 0, 0]
op5 = [0, 0, 0, 0, 0, 0]
op6 = [0, 0, 0, 0, 0, 0]
op7 = [0, 0, 0, 0, 0, 0]
op8 = [0, 0, 0, 0, 0, 0]
op9 = [0, 0, 0, 0, 0, 0]
op10 = [0, 0, 0, 0, 0, 0]
op11 = [0, 0, 0, 0, 0, 0]
op12 = [0, 0, 0, 0, 0, 0]
optCurr = 0
resLine = False   # Am I in a line where `"option n%string` is printed?
resCtr = 0        # Rotates within [0-4]
foundAbd = False  # For some configuration, has cvc5 been successful?
gettingAbd = False# Are we getting the 3 abducts?
abdCtr = 0        # Rotates within [0-3]
goalLine = False  # Am I in a line with the goal?
# Store each row for the CSV:
abds = ["", "", "", "", "", "", "", "", "", "", "", "", ""]
abdStr = ""
optCurrCnt = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
for j in f1lines:
  i = re.sub('\n', '', j)
  #Goal count
  if re.fullmatch(r'1 goal', i):
    numgoals += 1
  #Identify cvc5 configuration
  if re.fullmatch(r'\"option 1\"%string', i):
    optCurr = 1
    optCurrCnt[0] += 1
    resLine = True
  if re.fullmatch(r'\"option 2\"%string', i):
    optCurr = 2
    optCurrCnt[1] += 1
    resLine = True
  if re.fullmatch(r'\"option 3\"%string', i):
    optCurr = 3
    optCurrCnt[2] += 1
    resLine = True
  if re.fullmatch(r'\"option 4\"%string', i):
    optCurr = 4
    optCurrCnt[3] += 1
    resLine = True
  if re.fullmatch(r'\"option 5\"%string', i):
    optCurr = 5
    optCurrCnt[4] += 1
    resLine = True
  if re.fullmatch(r'\"option 6\"%string', i):
    optCurr = 6
    optCurrCnt[5] += 1
    resLine = True
  if re.fullmatch(r'\"option 7\"%string', i):
    optCurr = 7
    optCurrCnt[6] += 1
    resLine = True
  if re.fullmatch(r'\"option 8\"%string', i):
    optCurr = 8
    optCurrCnt[7] += 1
    resLine = True
  if re.fullmatch(r'\"option 9\"%string', i):
    optCurr = 9
    optCurrCnt[8] += 1
    resLine = True
  if re.fullmatch(r'\"option 10\"%string', i):
    optCurr = 10
    optCurrCnt[9] += 1
    resLine = True
  if re.fullmatch(r'\"option 11\"%string', i):
    optCurr = 11
    optCurrCnt[10] += 1
    resLine = True
  if re.fullmatch(r'\"option 12\"%string', i):
    optCurr = 12
    optCurrCnt[11] += 1
    resLine = True
  #Identify case
  if re.search(r'goal is invalid',i):
    updateRes(0, optCurr)
  if re.search(r'returned UNSAT',i):
    updateRes(1, optCurr)
  if re.search(r'can only deal with',i):
    updateRes(2, optCurr)
  if re.search(r'not reconstruct abduct',i):
    updateRes(3, optCurr)
  if re.search(r'is not of the expected type',i):
    updateRes(4, optCurr)
  if re.search(r'non-linear fact', i):
    updateRes(5, optCurr)

  #Get goal and abducts
  #Increment counter to check result
  if resLine:
    resCtr += 1
    if resCtr == 5:
      if re.search(r'goal is invalid', i):
        foundAbd = True
      else:
        foundAbd = False
    if resCtr == 6:
      resCtr = 0
      resLine = False
      if foundAbd:
        gettingAbd = True
  #Save goal
  if goalLine:
    writeCSV(abds, f2)
    abds = [i, "", "", "", "", "", "", "", "", "", "", "", ""]
    goalLine = False
  if re.search(r'====',i):
    goalLine = True
  #Save abducts
  if gettingAbd:
    if(abdCtr < 2):
      abdStr = abdStr + i + " | "
    if(abdCtr == 2):
      abdStr = abdStr + i
      abds[optCurr] = abdStr
      abdStr = ""
      gettingAbd = False
      abdCtr = 0
    abdCtr += 1
f1.close()

fcntopname = "ZorderAllCnts.csv" #input('Enter file name for count output: ')
f3 = open(fcntopname, "w")
f3.write("Option, # get-abd successes, # smt successes, # non-bool equality failures, # abd reconstructr failures, # atom unexp type failures, # non-linear failures\n")
f3.write("1," + str(op1[0]) + "," + str(op1[1]) + "," + str(op1[2]) + "," + str(op1[3]) + "," + str(op1[4]) + "," + str(op1[5]) + "\n")
f3.write("2," + str(op2[0]) + "," + str(op2[1]) + "," + str(op2[2]) + "," + str(op2[3]) + "," + str(op2[4]) + "," + str(op2[5]) + "\n")
f3.write("3," + str(op3[0]) + "," + str(op3[1]) + "," + str(op3[2]) + "," + str(op3[3]) + "," + str(op3[4]) + "," + str(op3[5]) + "\n")
f3.write("4," + str(op4[0]) + "," + str(op4[1]) + "," + str(op4[2]) + "," + str(op4[3]) + "," + str(op4[4]) + "," + str(op4[5]) + "\n")
f3.write("5," + str(op5[0]) + "," + str(op5[1]) + "," + str(op5[2]) + "," + str(op5[3]) + "," + str(op5[4]) + "," + str(op5[5]) + "\n")
f3.write("6," + str(op6[0]) + "," + str(op6[1]) + "," + str(op6[2]) + "," + str(op6[3]) + "," + str(op6[4]) + "," + str(op6[5]) + "\n")
f3.write("7," + str(op7[0]) + "," + str(op7[1]) + "," + str(op7[2]) + "," + str(op7[3]) + "," + str(op7[4]) + "," + str(op7[5]) + "\n")
f3.write("8," + str(op8[0]) + "," + str(op8[1]) + "," + str(op8[2]) + "," + str(op8[3]) + "," + str(op8[4]) + "," + str(op8[5]) + "\n")
f3.write("9," + str(op9[0]) + "," + str(op9[1]) + "," + str(op9[2]) + "," + str(op9[3]) + "," + str(op9[4]) + "," + str(op9[5]) + "\n")
f3.write("10," + str(op10[0]) + "," + str(op10[1]) + "," + str(op10[2]) + "," + str(op10[3]) + "," + str(op10[4]) + "," + str(op10[5]) + "\n")
f3.write("11," + str(op11[0]) + "," + str(op11[1]) + "," + str(op11[2]) + "," + str(op11[3]) + "," + str(op11[4]) + "," + str(op11[5]) + "\n")
f3.write("12," + str(op12[0]) + "," + str(op12[1]) + "," + str(op12[2]) + "," + str(op12[3]) + "," + str(op12[4]) + "," + str(op12[5]) + "\n")
print("Sanity checks:")
print("Total number of goals is " + str(numgoals))
print("Total number of goals from option 1 is " + str(optCurrCnt[0]))
print("Total number of goals from option 2 is " + str(optCurrCnt[1]))
print("Total number of goals from option 3 is " + str(optCurrCnt[2]))
print("Total number of goals from option 4 is " + str(optCurrCnt[3]))
print("Total number of goals from option 5 is " + str(optCurrCnt[4]))
print("Total number of goals from option 6 is " + str(optCurrCnt[5]))
print("Total number of goals from option 7 is " + str(optCurrCnt[6]))
print("Total number of goals from option 8 is " + str(optCurrCnt[7]))
print("Total number of goals from option 9 is " + str(optCurrCnt[8]))
print("Total number of goals from option 10 is " + str(optCurrCnt[9]))
print("Total number of goals from option 11 is " + str(optCurrCnt[10]))
print("Total number of goals from option 12 is " + str(optCurrCnt[10]))
print("Sum of option 01 goals is " + str(op1[0] + op1[1] + op1[2] + op1[3] + op1[4] + op1[5]))
print("Sum of option 02 goals is " + str(op2[0] + op2[1] + op2[2] + op2[3] + op2[4] + op2[5]))
print("Sum of option 03 goals is " + str(op3[0] + op3[1] + op3[2] + op3[3] + op3[4] + op3[5]))
print("Sum of option 04 goals is " + str(op4[0] + op4[1] + op4[2] + op4[3] + op4[4] + op4[5]))
print("Sum of option 05 goals is " + str(op5[0] + op5[1] + op5[2] + op5[3] + op5[4] + op5[5]))
print("Sum of option 06 goals is " + str(op6[0] + op6[1] + op6[2] + op6[3] + op6[4] + op6[5]))
print("Sum of option 07 goals is " + str(op7[0] + op7[1] + op7[2] + op7[3] + op7[4] + op7[5]))
print("Sum of option 08 goals is " + str(op8[0] + op8[1] + op8[2] + op8[3] + op8[4] + op8[5]))
print("Sum of option 09 goals is " + str(op9[0] + op9[1] + op9[2] + op9[3] + op9[4] + op9[5]))
print("Sum of option 10 goals is " + str(op10[0] + op10[1] + op10[2] + op10[3] + op10[4] + op10[5]))
print("Sum of option 11 goals is " + str(op11[0] + op11[1] + op11[2] + op11[3] + op11[4] + op11[5]))
print("Sum of option 12 goals is " + str(op12[0] + op12[1] + op12[2] + op12[3] + op12[4] + op12[5]))
f2.close()
f3.close()
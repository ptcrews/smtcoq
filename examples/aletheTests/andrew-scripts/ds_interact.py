###################################
#
#	Library for SMT debugging with COQ
#	LMF, CNRS & Universite Paris-Saclay
#
#   Copyright 2022-2023
#	Authors: Andrei Samokish, Dmitry Shintyakov
#
###################################

import subprocess
import threading
#from Queue import Queue, Empty
import queue
from time import sleep
import time


def _pipe_reader(stream, queue, name="thread"):
    #assert isinstance(queue, Queue)
    def reader():
        #print "Reader thread {} started".format(name)
        for line in iter(stream.readline, ''):
            if not line:
                break
            #print ("#### {} read line: {}".format(name, repr(line)))
            queue.put(line.decode("ASCII"))
        #print ("Input stream {} termanated, waiting for queue to empty".format(name))
        #queue.join()
        print ("{} terminated".format(name))
    return reader

class InteractiveProcess(object):
    def __init__(self, commandline, cwd = None):
        self.process = subprocess.Popen(commandline, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd = cwd, shell=True)
        self.q_stdout = queue.Queue(maxsize=1000)
        self.q_stderr = queue.Queue(maxsize=1000)

        self.stdin_reader = threading.Thread(target=_pipe_reader(self.process.stdout, self.q_stdout, "stdout"))
        self.stderr_reader = threading.Thread(target=_pipe_reader(self.process.stderr, self.q_stderr, "stderr"))
        self.stdin_reader.start()
        self.stderr_reader.start()

    
    # review reading function: accumulate till get non-empty result
    def read(self, poll_interval=0.05, input = input):
        stdout = []
        stderr = []
        gotSomething = False
        finishing = False
        start_time = time.time()
        while not finishing:
            empty = True
            try:
                data = self.q_stdout.get(timeout=0.001)
                if data:
                    gotSomething = True
                stdout.append(data)
                empty = False
            except queue.Empty: pass
            try:
                err = self.q_stderr.get(timeout=0.001)
                if err:
                    gotSomething = True
                stderr.append(err)
                empty = False
            except queue.Empty: pass

            if empty and gotSomething:
                #print "#### End of interactive reading"
                finishing = True
                break
            if (time.time() - start_time) > 100:
                print ('TIMEOUT!')
                print (input)

        return "".join(stdout), "".join(stderr)
    
    def readDS(self, poll_interval=0.05):
        stdout = []
        stderr = []
        while True:
            empty = True
            try:
                stdout.append(self.q_stdout.get(timeout = poll_interval))
                empty = False
            except Empty: pass
            try:
                stderr.append(self.q_stderr.get(timeout = poll_interval))
                empty = False
            except Empty: pass

            if empty and (stdout or stderr):
                #print "#### End of interactive reading"
                break
        return "".join(stdout), "".join(stderr)


    def interact(self, input="", poll_interval=0.05):
        if input:
            self.process.stdin.write(str.encode(input))
            self.process.stdin.flush()
        return self.read(poll_interval=poll_interval, input = input)
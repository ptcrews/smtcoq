#Take an op.txt file and return a csv classifying the results
#!/usr/bin/python3
import re

def writeCSV(l,f):
  line = ""
  if(l != ["", "", ""]):
    for i in l:
      line += (str(i) + "`")
    line += "\n"
    f.write(line)

def writeCSV2(l,f):
  for i in l:
    writeCSV(i, f)

fipname = input('Enter file (with relative path) to search: ')
f1 = open(fipname, "r")
f1lines = f1.readlines()
print("Total number of lines in input file is " + str(len(f1lines)))

fabdopname = input('Enter file name for abducts output: ')
f2 = open(fabdopname, "w")
f2.write("#` Goal` Abducts\n")
#number of goals in the file
numGoals = 0
#[# get-abd successes, # smt successes, # non-bool equality failures, # abd reconstructr failures, # atom unexp type failure, # non-linear failure]
op = [0, 0, 0, 0, 0, 0]
resLine = False   # Am I in a line where `goal is invalid` is printed?
resCtr = 0        # Rotates within [0-4]
gettingAbd = False# Are we getting the 3 abducts?
abdCtr = 0        # Rotates within [0-3]
goalLine = False  # Am I in a line with the goal?
# Store each row for the CSV, or combo of 3 rows for successful rows:
abds = [["", "", ""], 
        ["", "", ""],
        ["", "", ""]]
for j in f1lines:
  i = re.sub('\n', '', j)
  #Goal count
  if re.fullmatch(r'1 subgoal', i):
    numGoals += 1
    resLine = False
  #Identify case
  if re.search(r'goal is invalid', i):
    op[0] += 1
    resLine = True
    resCtr = 0
  if re.search(r'returned UNSAT', i):
    op[1] += 1
  if re.search(r'can only deal with', i):
    op[2] += 1
  if re.search(r'not reconstruct abduct', i):
    op[3] += 1
  if re.search(r'is not of the expected type', i):
    op[4] += 1
  if re.search(r'non-linear fact', i):
    op[5] += 1

  
  #Get goal and abducts
  
  #Increment counter to check result
  if resLine:
    resCtr += 1
    if resCtr == 3:
      gettingAbd = True
      
  #Save goal
  if goalLine:
    writeCSV2(abds, f2)
    abds = [[str(numGoals), i, ""], 
            ["", "", ""], 
            ["", "", ""]]
    goalLine = False
  if re.search(r'====',i):
    goalLine = True
  #Save abducts
  if gettingAbd:
    abds[abdCtr][2] = i
    if(abdCtr == 2):
      gettingAbd = False
      abdCtr = -1
    abdCtr += 1
writeCSV2(abds, f2)
f2.close()
f1.close()

fcntopname = input('Enter file name for count output: ')
f3 = open(fcntopname, "w")
f3.write("# goals, # get-abd successes, # get-abd success %, # smt successes, #smt success %, # non-bool equality failures, # abd reconstructr failures, # atom unexp type failures, # non-linear failures\n")
f3.write(str(numGoals) + "," + str(op[0]) + ",="+str(op[0])+"/"+str(numGoals) + "," + str(op[1]) + ",="+str(op[1])+"/"+str(numGoals) + "," + str(op[2]) + "," + str(op[3]) + "," + str(op[4]) + "," + str(op[5]) + "\n")
f3.close()
print("Sanity checks:")
print("Total number of goals is " + str(numGoals))
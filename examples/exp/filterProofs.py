#!/usr/bin/python3
import re

fipname = input('Enter file (with relative path) to search: ')
f1 = open(fipname, "r")
f1lines = f1.readlines()
print("Total number of lines in input file is " + str(len(f1lines)))

fopname = input('Enter output file name: ')
f2 = open(fopname, "w")

inproof = False
inproofhead = False
inproofbody = False
totalproofs = 0
totalsmallproofs = 0
aproofhead = []
aproofbody = []
length = 0
for i in f1lines:
  #Head of proof - lemma statement
  if re.search(r'Lemma|Theorem|Remark', i):
    totalproofs += 1
    inproof = True
    inproofhead = True
  #Body of proof - proof term
  if re.search(r'Proof', i) and inproof:
    inproofhead = False
    inproofbody = True
  if inproof:
    #Store proof head/body
    if inproofhead:
      aproofhead.append(i)
    if inproofbody:
      length += 1
      aproofbody.append(i)
  else:
    #Write non-proof code as-is
    f2.write(i)
  #End of proof
  if re.search(r'Qed\.|Defined\.', i) and inproof:
    inproof = False
    inproofbody = False
    #Write proof head
    for i in aproofhead:
      f2.write(i)
    #For small proofs, write abduction body
    if (length < 4):
      totalsmallproofs += 1
      f2.write("Proof. Show. Fail (cvc5_abduct 3). Admitted.\n")
    #For large proofs, write proof body
    else:
      for i in aproofbody:
        f2.write(i)
    aproofhead = []
    aproofbody = []
    length = 0
f1.close()
f2.close()

print("Total number of proofs is " + str(totalproofs))
print("Total number of proofs with < 5 lines is " + str(totalsmallproofs))

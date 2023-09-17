#!/usr/bin/python3

import re
import os

csv = open("list.csv", "w")
csv.write("Name, Formula, #Occurrences\n")

coq = open("List.v", "r")
listv = coq.read()

#Find all occurrences of "Theorem thname thform." or "Lemma thname thform."
th = re.findall(r"Theorem (\w+) .*\.", listv)
le = re.findall(r"Lemma (\w+) .*\.", listv)
thle = th + le
for i in thle:
  stream = os.popen('grep -c ' + i + ' List.v')
  cnt=stream.read()
  csv.write(i + "," + cnt)
csv.close()
coq.close()
#  cnt=grep -c "$thname" List.v
#

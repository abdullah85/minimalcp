# This file generates the second order formulae
#      for each agent for handsizes in [4,10]

from extractor import *

hashes = '################################################################'
def spacer():
  print
  print hashes
  print

def printMessage(msg):
  spacer()
  print msg
  spacer()

for i in range(4,11):
  printMessage('Obtaining lKObj for hSize : '+str(i))
  %time lObj = getLkObj(i)
  for agt in lObj.agents:
    printMessage('Generating optimized file for agt : '+agt)
    %time writeAgtFml(lObj, agt)

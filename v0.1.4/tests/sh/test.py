#!/usr/bin/python
from z3x86init import *
from genRuns import *
import time
x = time.time()
tabulateExperiments('1-',1, 3, 5, 100, 3)
y = time.time()
secs = y-x
print 'Took ',str(y-x),' seconds'

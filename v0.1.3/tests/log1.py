from leakageSadi import *
%time iLst = ImplicandLst(pLst, hLst);%time fLst = getFinalList(iLst)solver.push()solver = z3.Solver()solver.push()for f in fLst:
    solver.add(f)
    solver.push()gEq5 = z3.AtLeast(nHandLst(5))solver.add(gEq5)%time solver.check()#[Out]# sat
%magicls%logstart -r -o -t gEq6Log.py append%logstop
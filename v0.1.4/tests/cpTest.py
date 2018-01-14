from cpState import *
import os,time

a,b,c,e = 'a', 'b', 'c ', 'e'
infAgts = ['a', 'b', 'c']; 
eaves   = 'e';

class cpTest:
  def __init__(self, distrLst, agtLst):
    agtLst.sort()
    deal  = {}
    fCard = 0
    i = 0
    for agt in agtLst:
      deal[agt] = range(fCard, fCard + distrLst[i])
      fCard     = fCard + distrLst[i]
      i         = i+1
    self.agents = agtLst
    infAgts = self.agents[:-1]
    eaves   = self.agents[-1]
    self.s0        = cpState(distrLst, agtLst, deal, infAgts, eaves)
    self.timeStamp = time.strftime('%Y%m%d-%H%M%S')

  def genExecutions(self, destDir, filePref, hSize, annLen, runLen, nRuns, nBatch):
    s0 = self.s0
    for b in range(0,nBatch):
      runL, infL, summL  = [], [], []
      self.timeStamp = time.strftime('%Y%m%d-%H%M%S')
      fName = filePref+self.timeStamp
      tmpFile = destDir+'/'+fName+'.tmp' 
      dstFile = destDir+'/'+fName+'.log'
      f = open(tmpFile, 'w')
      f.write('# genExecutions \t: <destDir \t, hSize , aLen , rLen, nRuns, nBatch>\n')
      args = '# Args             \t: <'+destDir+' \t, '+str(hSize)+' \t, '+ str(annLen)+ ' \t, '
      args = args  + str(runLen)+ ' \t, '+str(nRuns)+' \t, '+str(nBatch)+' \t>'
      args = args+'\n'
      for n in range(0, nRuns):
        run  = s0.genRun(hSize, annLen, runLen)
        sF   = s0.execRun(run)
        (summary, infFor, nInfFor) = s0.extractAllPos()
        runL.append(run)
        infL.append(infFor)
        summL.append(summary)
      # Output generation ...
      self.timeStamp = time.strftime('%Y%m%d-%H%M%S')
      fName = filePref+self.timeStamp+'.log'
      f = open(destDir+'/'+fName, 'w')
      for i in range(0,len(runL)):
        f.write(str(runL[i]) +'\n')
        f.write(';\n')
        f.write(str(infL[i]) +'\n')
        f.write(';\n')
        summary = summL[i]
        kLst = summary.keys()
        kLst.sort()
        f.write('{\n')
        for k in kLst:
          f.write('\''+k+'\''+' : '+str(summary[k]))
          if k != kLst[:-1]:
            f.write(',')
          f.write('\n')
        f.write('}\n')
        f.write('\n')
      f.close()
      os.system('mv '+tmpFile+' '+dstFile)
    print 'Completed !!!'
    return (runL, infL, summL)

  def genEavesSummary(self, destDir, filePref, hSize, annLen, runLen, nRuns, nBatch):
    '''
    Unlike genExecutions, here we generate only summary for eavesdropper.
    '''
    s0 = self.s0
    eaves = self.s0.eaves
    for b in range(0,nBatch):
      runL, infL, summL  = [], [], []
      self.timeStamp = time.strftime('%Y%m%d-%H%M%S')
      fName   = filePref+self.timeStamp
      tmpFile = destDir+'/'+fName+'.tmp' 
      dstFile = destDir+'/'+fName+'.log'
      f = open(tmpFile, 'w')
      f.write('# genEavesSummary \t: <destDir \t, hSize , aLen , rLen, nRuns, nBatch>\n')
      args = '# Args             \t: <'+destDir+' \t, '+str(hSize)+' \t, '+ str(annLen)+ ' \t, '
      args = args  + str(runLen)+ ' \t, '+str(nRuns)+' \t, '+str(nBatch)+' \t>'
      args = args+'\n'
      f.write(args)
      for n in range(0, nRuns):
        run  = s0.genRun(hSize, annLen, runLen)
        sF   = s0.execRun(run)
        (summary, infFor, nInfFor) = sF.extractPosFor(eaves)
        runL.append(run)
        infL.append(infFor)
        summL.append(summary)
      #     Output generation ...
      for i in range(0, len(runL)):
        self.writeRun(f, runL[i])
        f.write(';\n')
        f.write(str(infL[i]) +'\n')
        f.write(';\n')
        summary = summL[i]
        f.write(str(summary)+'\n')
        f.write('\n')  
      f.close()
      os.system('mv '+tmpFile+' '+dstFile)
    print 'Completed !!!'
    return (runL, infL, summL)

  def composeEavesSummary(self, srcD1, srcF1, srcD2, srcF2, tgtD, tgtF):
    rL1, iL1, sL1 = self.extractLists(srcD1, srcF1)
    rL2, iL2, sL2 = self.extractLists(srcD2, srcF2)
    compRuns = []
    for r1 in rL1:
      for r2 in rL2:
        newRun = []
        for ann in r1:
          newRun.append(ann)
        for ann in r2:
          newRun.append(ann)
        compRuns.append(newRun)
    tmpFile = tgtD+'/'+tgtF+'.tmp'
    dstFile = tgtD+'/'+tgtF+'.txt'
    f = open(tmpFile,'w')
    f.write('# composeEavesSummary \t: <srcD1 \t, srcF1, srcD2 , srcF2, tgtD, tgtF>\n')
    args = '# Args             \t: <'+srcD1+' \t, '+srcF1+' \t, '+ srcD2+ ' \t, ' + srcF2+'\t>'
    args = args+'\n'
    f.write(args)
    s0 = self.s0
    eaves = self.s0.eaves
    runL, infL, summL = [], [], []
    for cRun in compRuns:
      sF   = s0.execRun(cRun)
      (summary, infFor, nInfFor) = sF.extractPosFor(eaves)      
      runL.append(cRun)
      infL.append(infFor)
      summL.append(summary)
    for i in range(0,len(runL)):
      f.write(str(runL[i]) +'\n')
      f.write(';\n')
      f.write(str(infL[i]) +'\n')
      f.write(';\n')
      summary = summL[i]
      f.write(str(summary)+'\n')
      f.write('\n')  
    f.close()
    os.system('mv '+tmpFile+' '+dstFile)             

  def writeSummary(self, f, summary):
    kLst = summary.keys()
    kLst.sort()
    f.write('{\n')
    for k in kLst:
      f.write('\''+k+'\''+' : '+str(summary[k]))
      if k != kLst[:-1]:
        f.write(',')
      f.write('\n')
    f.write('}\n')

  def writeRun(self, f, run):
    f.write('[\n')
    for ann in run:      
      f.write('  '+str(ann))
      if ann != run[-1]:
        f.write(',')
      f.write('\n')
    f.write(']\n')

  def mergeFiles(self, srcDir, srcPrefix, srcType, tgtDir, tgtName, tgtType):
    '''
    merge all files starting with srcPrefix and ending in .srcType
    to a single file at tgtDir/tgtName.tgtType. For instance

    >>> report = cpReport([4,4,4,0], ['a', 'b', 'c', 'e'])
    >>> srcDir = 'results/4440/030305100/'
    >>> report.mergeFiles(srcDir, '1-', 'txt', srcDir, 'one-complete', 'txt')

    should return a file called results/4440/030305100/one-complete.txt.
    Note the difference in target and source prefixes. This is to avoid some
    confusion if the function is run again on the same arguments.
    '''
    srcLst = []
    dirLst = os.listdir(srcDir)
    dirLst.sort()
    for fName in dirLst :
      if fName.startswith(srcPrefix) and fName.endswith(srcType):
        srcLst.append(fName)
    f = open(tgtDir+'/'+tgtName+'.'+tgtType, 'w')
    for srcFile in srcLst:
      fSrc = open(srcDir+'/'+srcFile, 'r')
      txt  = fSrc.read()
      f.write(txt)
    f.close()
    return srcLst

  def extractLists(self, srcDir, srcFile):
    '''
    Obtain execution info as three lists from srcDir/srcFile.srcType.
    '''
    f = open(srcDir+'/'+srcFile, 'r')
    txt = f.read()
    f.close()
    execLst = txt.split('\n\n')
    execLst = execLst[:-1]
    runL, infL, summL = [], [], []
    for execInfo in execLst:
      r,i,s = execInfo.split(';')
      runL.append(eval(r))
      infL.append(eval(i))
      summL.append(eval(s))
    return (runL, infL, summL)

  def getInfSummary(self, srcDir, srcFile):
    runL, infL, propsL = self.extractLists(srcDir, srcFile)
    infKeys = []
    for iL in infL:
      key = ''.join(iL)
      infKeys.append(key)
    kLst = list(set(infKeys))
    kLst.sort()
    kLst.sort(key=len)
    summary = {}    
    for k in kLst:
      summary[k] = []
    for i in range(0,len(infL)):
      key = ''.join(infL[i])
      summary[key].append(i)
    return (summary, runL, propsL)

  def genInfSummList(self, srcDir, srcPrefix, srcType):
    srcLst = []
    dirLst = os.listdir(srcDir)
    dirLst.sort()
    for fN in dirLst:
      if fN.startswith(srcPrefix):
        if fN.endswith(srcType):
          srcLst.append(fN)
    summLst = []
    runLst  = []
    propsLst = []
    for f in srcLst:
      summary,runL, propsL = (self.getInfSummary(srcDir, f))
      summLst.append(summary)
      runLst.append(runL)
      propsLst.append(propsL)
    return (summLst, runLst, propsLst)

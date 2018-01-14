from cpState import *
import os, time

a,b,c,e = 'a', 'b', 'c', 'e'
infAgts = ['a', 'b', 'c']; 
eaves   = 'e';

class cpReport:
  '''
  For preparing reports, tables and the like from the 
  output of cpTest.py functions.
  '''
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
    self.s0 = cpState(distrLst, agtLst, deal, infAgts, eaves)
    self.timeStamp = time.strftime('%Y%m%d-%H%M%S')

  def key2Set(self, key):
    if key  == '' :
      return  ' $ \quad \\emptyset \quad$ '
    sName = ' $  '
    agts = list(key)
    for i in range(0, len(agts)):
      ag = agts[i]
      sName = sName + ag.upper()
      if i != len(agts)-1:
        sName = sName + ', '
    sName = sName+ ' $ '
    return sName

  def genTableHeader(self, rHeader, kLst):
    tableHeader = '\\begin{tabular}{| c |' # This entry is for the row name
    prevLen = len(kLst[0])
    for k in kLst:
      if len(k) > prevLen :
        tableHeader = tableHeader + ' | '
        prevLen = len(k)
      tableHeader = tableHeader + ' c '
    tableHeader = tableHeader + '| }\n \\hline\n'
    tableCols = '' + rHeader + ' & '
    for i in range(0,len(kLst)):
      key = kLst[i]
      tableCols = tableCols + '$\;$' + self.key2Set(key) + '$\;$'
      if i != len(kLst) - 1:
        tableCols = tableCols + ' & \n'
    tableCols = tableCols + ' \\\\ [0.7ex]\n'
    tableHeader = tableHeader + tableCols
    tableHeader = tableHeader + '\\hline \n'
    return tableHeader

  def genEntry(self, kLst, summary):
    entry = ''
    summKeys = summary.keys()
    for i in range(0,len(kLst)):
      key = kLst[i]
      if not key in summKeys:
        entry = entry +' 0 '
      else:
        sLen = len(summary[key])
        entry = entry + ' ' +str(sLen) + ' '
      if i != len(kLst) - 1:
        entry = entry +' & '
    return entry

  def genBody(self, rowNames, kLst, summL):
    body = ''
    print rowNames
    print len(summL)
    for i in range(0,len(summL)):
      kL = summL[i].keys()
      kL.sort()
      kL.sort(key=len)
      print kL
    for i in range(0, len(summL)):
      summary = summL[i]
      body  = body + rowNames[i]+ ' & '
      entry = self.genEntry(kLst, summary)
      body  = body+ entry +'\\\\\n'
    return body

  def genTable(self, rHeader, rNames, summLst):
    kLst = []
    for summ in summLst:
      sKL = summ.keys()
      kLst = kLst + sKL 
    kLst = list(set(kLst))
    kLst.sort()
    kLst.sort(key=len)
    kLst = kLst # For describing the row
    tableHeader = self.genTableHeader(rHeader, kLst) 
    tableBody = self.genBody(rNames, kLst, summLst)
    tableFooter = '\\hline\n'+ '\\end{tabular}\n'
    tableTxt  = tableHeader + tableBody + tableFooter
    return tableTxt

  def getEavesSummary(self, propsL):
    kLst   = []
    for pL in propsL:
      nRevealed = len(pL)
      kLst.append(nRevealed)
    kLst = list(set(kLst))
    summary = {}
    for k in kLst:
      summary[k] = 0
    for pL in propsL:
      key = len(pL)
      summary[key] = summary[key] + 1
    total  = len(propsL) # Number of executions tried
    values = []
    for n in range(0, (self.s0.nCards + 1)):
      if n not in kLst:
        nR = 0
      else:
        nR = summary[n]
      percent = math.ceil((nR*100)/total)
      values.append(percent)
    return (summary, values)

  def getEavesCoords(self, propsL):
    s,v = self.getEavesSummary(propsL)
    coords = []
    for i in range(0, len(v)):
      coords.append((i, v[i]))
    coordsStr = ''
    for x in coords:
      coordsStr = coordsStr+' ' +str(x)
    return (coords, coordsStr)

  def getEavesPlot(self, coordsStr, color, mark, legendStr):
    plotStr = '\\addplot[\n'
    plotStr = plotStr +'color='+color+' ,'+ ' mark='+mark+',\n'+' ]'
    plotStr = plotStr + 'coordinates {\n' + coordsStr +'\n'
    plotStr = plotStr + '};\n'
    plotStr = plotStr+   "\\addlegendentry{"+ legendStr + '}\n'
    return plotStr

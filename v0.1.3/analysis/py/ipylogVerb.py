\begin{verbatim}
# IPython log file

import cpState as cps; import cpUtil  as ut ;
a,b,c,e = 'a', 'b', 'c', 'e'
dealLst = [4,4,4,0]; agtLst = [a, b, c, e];
d0 = ut.minDeal(dealLst, agtLst, range(12));
s0 = cps.cpState(dealLst, agtLst, d0, [a, b, c], e);

%run strategy1.py

r1 = getRun1(d0, [a,b,c])
r1
[('a',
  [[0, 1, 2, 3],  [0, 1, 2, 4],  [0, 1, 2, 6],  
   [0, 1, 3, 4],  [0, 1, 3, 6],  [0, 1, 4, 6],  
   [0, 2, 3, 4],  [0, 2, 3, 6],  [0, 2, 4, 6],  
   [0, 3, 4, 6],  [1, 2, 3, 4],  [1, 2, 3, 6],
   [1, 2, 4, 6],  [1, 3, 4, 6],  [2, 3, 4, 6]]),
 ('b',
  [[2, 4, 5, 6],  [2, 4, 5, 7],  [2, 4, 5, 10],  
   [2, 4, 6, 7],  [2, 4, 6, 10], [2, 4, 7, 10],  
   [2, 5, 6, 7],  [2, 5, 6, 10], [2, 5, 7, 10],  
   [2, 6, 7, 10],  [4, 5, 6, 7], [4, 5, 6, 10],
   [4, 5, 7, 10],  [4, 6, 7, 10],[5, 6, 7, 10]]),
 ('c',
  [[3, 4, 8, 9],   [3, 4, 8, 10],  [3, 4, 8, 11],  
   [3, 4, 9, 10],  [3, 4, 9, 11],  [3, 4, 10, 11],  
   [3, 8, 9, 10],  [3, 8, 9, 11],  [3, 8, 10, 11], 
   [3, 9, 10, 11], [4, 8, 9, 10],  [4, 8, 9, 11],
   [4, 8, 10, 11], [4, 9, 10, 11], [8, 9, 10, 11]]),
('a',
  [[0, 1, 2, 3],  [0, 1, 2, 4], [0, 1, 2, 6],  
   [0, 1, 3, 4],  [0, 1, 3, 6], [0, 1, 4, 6],  
   [0, 2, 3, 4],  [0, 2, 3, 6], [0, 2, 4, 6],  
   [0, 3, 4, 6],  [1, 2, 3, 4], [1, 2, 3, 6],
   [1, 2, 4, 6],  [1, 3, 4, 6], [2, 3, 4, 6]]),
('b',
  [[2, 4, 5, 6],  [2, 4, 5, 7],   [2, 4, 5, 10],  
   [2, 4, 6, 7],  [2, 4, 6, 10],  [2, 4, 7, 10],
   [2, 5, 6, 7],  [2, 5, 6, 10],  [2, 5, 7, 10],
   [2, 6, 7, 10],  [4, 5, 6, 7],  [4, 5, 6, 10],
   [4, 5, 7, 10],  [4, 6, 7, 10],  [5, 6, 7, 10]]),
('c',
  [[3, 4, 8, 9],   [3, 4, 8, 10],  [3, 4, 8, 11],  
   [3, 4, 9, 10],  [3, 4, 9, 11],  [3, 4, 10, 11],
   [3, 8, 9, 10],  [3, 8, 9, 11],  [3, 8, 10, 11],
   [3, 9, 10, 11], [4, 8, 9, 10],  [4, 8, 9, 11],
   [4, 8, 10, 11], [4, 9, 10, 11], [8, 9, 10, 11]])]   

r2 = getRun1(d0, [a,b,c])
r2
[('a',
  [[0, 1, 2, 3],  [0, 1, 2, 4],  [0, 1, 2, 5],  
   [0, 1, 3, 4],  [0, 1, 3, 5],  [0, 1, 4, 5],
   [0, 2, 3, 4],  [0, 2, 3, 5],  [0, 2, 4, 5],
   [0, 3, 4, 5],  [1, 2, 3, 4],  [1, 2, 3, 5],
   [1, 2, 4, 5],  [1, 3, 4, 5],  [2, 3, 4, 5]]),
 ('b',
  [[0, 1, 4, 5],  [0, 1, 4, 6],  [0, 1, 4, 7],
   [0, 1, 5, 6],  [0, 1, 5, 7],  [0, 1, 6, 7],
   [0, 4, 5, 6],  [0, 4, 5, 7],  [0, 4, 6, 7],
   [0, 5, 6, 7],  [1, 4, 5, 6],  [1, 4, 5, 7],
   [1, 4, 6, 7],  [1, 5, 6, 7],  [4, 5, 6, 7]]),
 ('c',
  [[6, 7, 8, 9],   [6, 7, 8, 10], [6, 7, 8, 11],
   [6, 7, 9, 10],  [6, 7, 9, 11], [6, 7, 10, 11],
   [6, 8, 9, 10],  [6, 8, 9, 11], [6, 8, 10, 11],
   [6, 9, 10, 11], [7, 8, 9, 10], [7, 8, 9, 11],
   [7, 8, 10, 11], [7, 9, 10, 11],  [8, 9, 10, 11]]),

('a', [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], 
       [0, 2, 3, 4], [1, 2, 3, 4]]),
 ('b',
  [[0, 1, 4, 5],  [0, 1, 4, 6],  [0, 1, 4, 7],  
   [0, 1, 5, 6],  [0, 1, 5, 7],  [0, 1, 6, 7],
   [0, 4, 5, 6],  [0, 4, 5, 7],  [0, 4, 6, 7],
   [0, 5, 6, 7],  [1, 4, 5, 6],  [1, 4, 5, 7],
   [1, 4, 6, 7],  [1, 5, 6, 7],  [4, 5, 6, 7]]),
 ('c',
  [[6, 7, 8, 9],   [6, 7, 8, 10], [6, 7, 8, 11],  
   [6, 7, 9, 10],  [6, 7, 9, 11], [6, 7, 10, 11],
   [6, 8, 9, 10],  [6, 8, 9, 11], [6, 8, 10, 11],
   [6, 9, 10, 11], [7, 8, 9, 10], [7, 8, 9, 11],
   [7, 8, 10, 11], [7, 9, 10, 11],[8, 9, 10, 11]])]
\end{verbatim}

As we can see in the above sample runs, $r1$ was such that the second round
was basically the same as the first round while for $r2$ the second
annoucement of $A$ was more informative than the first.

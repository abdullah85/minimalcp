from lk import *

doubleEntry = []                                            
for h in cHCount.keys():        
  if cHCount[h] > 1:      
    doubleEntry.append(h)

cDuplicates = []
for cH in doubleEntry:                                      
  cDuplicates.append(eval(cH))

cProbDeals = []
for d in cDeals:                                            
  if d[c] in cDuplicates:
    cProbDeals.append(d)
cProbDeals = ut.sortDeals_byLst(cProbDeals, ['c', 'b' ,'a'])
cProbDeals = [{'a': [0, 3, 4, 5], 'b': [2, 8, 10, 11], 'c': [1, 6, 7, 9]}, \
              {'a': [0, 2, 3, 5], 'b': [4, 8, 10, 11], 'c': [1, 6, 7, 9]}, \
              {'a': [0, 1, 4, 9], 'b': [2, 8, 10, 11], 'c': [3, 5, 6, 7]}, \
              {'a': [0, 1, 2, 9], 'b': [4, 8, 10, 11], 'c': [3, 5, 6, 7]}, \ 
              {'a': [0, 1, 4, 5], 'b': [2, 8, 10, 11], 'c': [3, 6, 7, 9]}, \
              {'a': [0, 1, 2, 5], 'b': [4, 8, 10, 11], 'c': [3, 6, 7, 9]}, \
              {'a': [0, 2, 3, 10], 'b': [1, 5, 8, 11], 'c': [4, 6, 7, 9]}, \
              {'a': [0, 1, 3, 5], 'b': [2, 8, 10, 11], 'c': [4, 6, 7, 9]}, \
              {'a': [0, 1, 3, 4], 'b': [2, 8, 10, 11], 'c': [5, 6, 7, 9]}, \
              {'a': [0, 1, 2, 3], 'b': [4, 8, 10, 11], 'c': [5, 6, 7, 9]}, \
              {'a': [0, 2, 3, 5], 'b': [1, 4, 10, 11], 'c': [6, 7, 8, 9]}, \
              {'a': [0, 1, 2, 5], 'b': [3, 4, 10, 11], 'c': [6, 7, 8, 9]}]

# What follows below are indices into the actual hand held by agents b and c.
# Fix ann1 above and ensure that deal i satisfies ann_i in the list below (i>=1).
s1AnnL = [[[447, 434, 489, 129, 265, 440, 445, 426, 282], [415, 438, 493, 417, 364, 442, 306, 324, 404]], \
          [[447, 434, 489, 129, 265, 440, 445, 427, 282], [415, 438, 417, 364, 442, 306, 492, 324, 404]], \
          [[451, 346, 428, 129, 265, 440, 330, 282, 455], [415, 452, 438, 413, 407, 491, 442, 210, 404]], \
          [[451, 346, 129, 265, 440, 429, 330, 282, 455], [415, 452, 438, 413, 407, 442, 490, 210, 404]], \
          [[451, 346, 129, 265, 440, 330, 282, 430, 455], [415, 452, 438, 489, 413, 407, 442, 210, 404]], \
          [[451, 346, 129, 265, 440, 431, 330, 282, 455], [415, 452, 438, 413, 407, 442, 210, 488, 404]], \
          [[451, 346, 129, 265, 440, 432, 330, 282, 455], [415, 452, 438, 487, 413, 407, 442, 210, 404]], \
          [[451, 346, 129, 265, 440, 330, 282, 433, 455], [415, 452, 438, 413, 407, 442, 486, 210, 404]], \
          [[451, 434, 346, 129, 265, 440, 330, 282, 455], [415, 452, 438, 413, 407, 442, 485, 210, 404]], \
          [[451, 320, 435, 129, 265, 440, 330, 282, 455], [415, 438, 420, 473, 413, 442, 210, 484, 404]], \
          [[451, 320, 365, 129, 265, 440, 436, 282, 455], [415, 438, 420, 413, 442, 483, 210, 404, 433]], \
          [[451, 320, 437, 365, 129, 265, 440, 282, 455], [415, 438, 482, 420, 413, 442, 210, 404, 433]], \
          [[451, 320, 365, 438, 129, 265, 440, 282, 455], [415, 438, 420, 413, 481, 442, 210, 404, 433]], \
          [[439, 451, 320, 365, 129, 265, 440, 282, 455], [415, 438, 420, 413, 480, 442, 210, 404, 433]], \
          [[451, 320, 365, 129, 265, 440, 282, 433, 455], [415, 438, 410, 420, 413, 442, 210, 479, 433]], \
          [[451, 320, 365, 129, 265, 282, 433, 441, 455], [415, 438, 478, 410, 420, 413, 442, 210, 433]], \
          [[451, 320, 365, 129, 265, 282, 442, 433, 455], [415, 438, 410, 420, 413, 442, 210, 433, 477]], \
          [[451, 320, 365, 129, 265, 443, 282, 433, 455], [415, 438, 476, 410, 420, 413, 442, 210, 433]], \
          [[451, 365, 444, 129, 265, 282, 433, 455], [415, 438, 475, 410, 413, 442, 210, 433]], \
          [[451, 347, 376, 129, 265, 445, 282, 455], [415, 438, 475, 413, 442, 210, 451, 474]], \
          [[446, 451, 347, 376, 129, 265, 282, 351, 455], [415, 438, 475, 473, 413, 442, 210, 451, 457]], \
          [[451, 447, 347, 129, 265, 386, 286, 282, 351, 455], [415, 438, 413, 462, 442, 472, 210, 492, 451, 457]], \
          [[451, 347, 448, 129, 265, 445, 286, 282, 351, 455], [415, 438, 398, 471, 413, 442, 210, 492, 451, 457]], \
          [[451, 347, 84, 379, 265, 286, 449, 282, 351, 455], [470, 438, 493, 471, 413, 442, 210, 492, 451, 457]], \
          [[450, 451, 347, 84, 265, 286, 449, 282, 351, 455], [438, 493, 413, 442, 469, 210, 492, 451, 457, 395]], \
          [[451, 471, 347, 84, 265, 378, 286, 282, 351, 455], [438, 493, 468, 491, 442, 379, 210, 492, 451, 457]], \
          [[471, 347, 84, 265, 378, 452, 286, 282, 351, 455], [438, 493, 491, 442, 379, 210, 467, 492, 451, 457]], \
          [[471, 347, 453, 84, 265, 378, 286, 282, 351, 455], [438, 493, 466, 491, 442, 379, 210, 492, 451, 457]], \
          [[471, 347, 454, 84, 265, 378, 286, 282, 351, 455], [438, 493, 465, 491, 442, 379, 210, 492, 451, 457]], \
          [[347, 363, 84, 265, 378, 445, 442, 455, 283, 358], [438, 493, 279, 401, 445, 380, 491, 370, 464, 451]], \
          [[347, 363, 84, 265, 378, 445, 456, 455, 283, 358], [391, 438, 493, 279, 445, 380, 491, 370, 463, 451]], \
          [[347, 363, 84, 265, 378, 445, 457, 455, 283, 358], [391, 438, 493, 279, 445, 380, 491, 462, 370, 451]], \
          [[347, 363, 84, 265, 378, 458, 445, 455, 283, 358], [391, 438, 493, 279, 445, 380, 491, 461, 370, 451]], \
          [[347, 363, 84, 265, 378, 445, 459, 455, 283, 358], [391, 438, 493, 279, 445, 380, 491, 370, 460, 451]], \
          [[460, 363, 276, 84, 248, 378, 445, 360, 455, 358], [391, 459, 438, 493, 279, 445, 380, 491, 460, 374]], \
          [[363, 276, 84, 248, 378, 461, 445, 360, 395, 358], [438, 493, 279, 445, 380, 491, 458, 449, 460, 374]], \
          [[363, 276, 84, 248, 378, 445, 360, 462, 395, 358], [438, 493, 279, 445, 380, 491, 449, 460, 457, 374]], \
          [[363, 276, 84, 248, 378, 445, 360, 462, 358, 463], [438, 386, 493, 279, 445, 380, 491, 456, 460, 374]], \
          [[363, 276, 84, 248, 378, 445, 464, 360, 462, 358], [438, 386, 493, 279, 445, 455, 380, 491, 460, 374]], \
          [[465, 363, 276, 84, 248, 378, 445, 360, 462, 358], [438, 386, 454, 493, 279, 445, 380, 491, 460, 374]], \
          [[363, 276, 84, 466, 248, 378, 445, 360, 462, 358], [438, 386, 493, 279, 445, 453, 380, 491, 460, 374]], \
          [[363, 276, 84, 248, 378, 445, 467, 360, 462, 358], [452, 438, 386, 493, 279, 445, 380, 491, 460, 374]], \
          [[363, 276, 84, 468, 248, 378, 445, 360, 462, 358], [438, 386, 493, 279, 445, 380, 491, 460, 451, 374]], \
          [[333, 363, 276, 84, 469, 248, 378, 445, 360, 462], [438, 405, 386, 450, 493, 279, 445, 491, 460, 374]], \
          [[333, 363, 276, 84, 470, 248, 378, 445, 394, 360], [438, 405, 493, 279, 445, 491, 449, 460, 451, 374]], \
          [[333, 471, 362, 363, 84, 248, 261, 378, 445, 394], [382, 405, 493, 279, 445, 448, 436, 491, 460, 451]], \
          [[333, 362, 472, 363, 84, 248, 261, 378, 445, 394], [382, 405, 493, 279, 445, 436, 447, 491, 460, 451]], \
          [[333, 347, 363, 84, 473, 248, 261, 378, 445, 401], [382, 405, 493, 279, 445, 446, 491, 442, 460, 451]], \
          [[333, 474, 347, 84, 248, 261, 378, 445, 397], [382, 405, 493, 279, 445, 446, 491, 460, 451]], \
          [[333, 347, 475, 84, 248, 261, 378, 445, 356, 397], [452, 382, 405, 493, 279, 446, 491, 444, 460, 451]], \
          [[404, 347, 84, 248, 261, 378, 445, 476, 356, 305], [452, 382, 493, 279, 440, 443, 446, 491, 460, 451]], \
          [[404, 347, 84, 248, 261, 378, 445, 356, 305, 477], [452, 382, 493, 279, 440, 446, 491, 442, 460, 451]], \
          [[362, 347, 276, 84, 416, 248, 378, 445, 355, 478], [382, 493, 279, 446, 491, 429, 460, 451, 441, 374]], \
          [[362, 347, 276, 84, 416, 479, 248, 378, 445, 355], [382, 493, 279, 440, 446, 491, 429, 460, 451, 374]], \
          [[362, 347, 276, 84, 416, 248, 378, 445, 355, 480], [382, 439, 493, 279, 446, 491, 429, 460, 451, 374]], \
          [[333, 481, 362, 84, 378, 445, 355, 234], [382, 470, 438, 493, 279, 446, 491, 416]], \
          [[482, 362, 84, 378, 445, 355, 234, 360], [382, 438, 493, 279, 446, 491, 416, 437]], \
          [[363, 84, 378, 445, 355, 483, 234, 360], [382, 438, 493, 279, 445, 436, 491, 416]], \
          [[84, 359, 378, 484, 445, 355, 234, 360], [382, 438, 493, 279, 435, 491, 416, 449]], \
          [[485, 84, 359, 378, 445, 355, 234, 360], [382, 438, 493, 279, 434, 491, 416, 449]], \
          [[84, 359, 378, 445, 355, 234, 360, 486], [382, 438, 493, 279, 491, 416, 449, 433]], \
          [[84, 359, 378, 445, 487, 234, 360], [438, 493, 279, 432, 491, 416, 449]], \
            [[84, 359, 378, 445, 234, 360, 488], [438, 493, 279, 431, 491, 416, 449]], \
          [[489, 84,59, 378, 445, 234, 360], [438, 493, 279, 430, 491, 416, 449]], \
          [[490, 84, 359, 378, 445, 234, 360], [438, 493, 279, 491, 416, 449, 429]], \
          [[84, 359, 378, 445, 234, 491, 360], [438, 493, 279, 428, 491, 416, 449]], \
          [[492, 84,59, 378, 445, 234, 360], [438, 493, 279, 491, 416, 427, 449]], \
          [[404, 84, 359, 378, 445, 493, 234, 360], [438, 493, 279, 440, 491, 416, 449, 426]], \
          [[404, 84, 359, 378, 494, 445, 234, 360], [438, 493, 279, 440, 425, 491, 416, 449]]] 


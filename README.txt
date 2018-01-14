# minimalcp

* Instructions for running on linux

In what follows let $cp denote the location of this folder
and version be $version (current version is v0.1.4/).

To run cp version, we need to

1) Link z3 appropriately (See below)
2) update PYTHONPATH appropriately to link to cp source ($
   * export PYTHONPATH=$PYTHONPATH:$cp/$version/src/cp
3) For running tests, add
   * export PYTHONPATH=$PYTHONPATH:$cp/$version/tests 

### Linking z3

 Let $cp be the location of repository and let 
$z3Version be the appropriate version of z3 to
be used. Then,

a) extract the relevant version of z3 into $cp/z3/$z3Version
b) export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$cp/z3/$z3Version/bin
c) export PYTHONPATH=$cp/z3/$z3Version/bin/python

Save commands b) and c) in appropriate .bashrc file.


v0.1.3 represents a greatly improved as well as simplified 
version of the update mechanism by an alternative representation 
of the knowledge base of each agent.

To use z3 on ubuntu :

Let $cp be the location of repository and let 
$z3Version be the appropriate version of z3 to
be used. Then,

a) extract the relevant version of z3 into $cp/z3/$z3Version
b) export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$cp/z3/$z3Version/bin
c) export PYTHONPATH=$cp/z3/$z3Version/bin/python

Save commands b) and c) in appropriate .bashrc file.

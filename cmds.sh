export cp=~/Desktop/minimalcp
export setup=~/Desktop/setup
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$setup/z3/build/python
export PYTHONPATH=$PYTHONPATH:$setup/z3/build/python
export PYTHONPATH=$PYTHONPATH:$cp/v0.1.3/src/cp
export PYTHONPATH=$PYTHONPATH::$cp/v0.1.3/tests
source $setup/z3/venv/bin/activate

In order to run the tests, include the
appropriate cp package location in the
PYTHONPATH variable, (for ubuntu)

export PYTHONPATH=$PYTHONPATH:$rus/v01.3/src/cp

where $rus is the location of the repository.

In addition, we also need to have the
requirements to load the z3 package 
appropriately (See ../README.txt).

To install and run pytest we need to
a) install virtualenv (Easiest way is $sudo pip install virtualenv)
b) Create a local virtual environment 
   $ cd $rus/v0.1.3
   $ virtualenv env
   $ env/bin/pip install pytest
c) Use source to change default python 
   $ source env/bin/activate # Save in .bashrc if needed)
   $ which python            # To check
   $ deactivate              # To return to original setting

For more on pip and virtualenv, see
https://www.dabapps.com/blog/introduction-to-pip-and-virtualenv-python/

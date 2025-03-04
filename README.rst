**pyeb** is a Python implementation of Event-B's refinement calculus. It takes an Event-B model as
an input and generates proof-obligations that are eventually discharged with the Z3 SMT
solver. Event-B models are written in Python following a special Object-Oriented syntax and
notation. The **pyeb** tool generates proof obligations such as invariant preservation, feasibility
of non-deterministic event actions, guard strengthening, simulation, preservation of machine
variants, among others.  **pyeb** uses `Z3 Python API
<https://z3prover.github.io/api/html/namespacez3py.html>`_ to discharge the proof obligations
automatically. It supports large parts of Event-B' syntax such as non-deterministic assignments,
events, machines, contexts, and machine refinements. **pyeb** is implemented as a library and. It is hosted `here <https://pypi.org/project/pyeb/>`_. 

As future work, we plan to support code generation for **pyeb** models into Python and Rust
programming languages. Our future work on code generation will focus on two axes: *(i.)* we plan to
generate code for sequential programs as described by J.-R. Abrial `here
<https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/122/>`_, and *(ii.)* we plan
to generate code for concurrent reactive systems similar to the approach followed by the
`EventB2Java tool <https://link.springer.com/article/10.1007/s10009-015-0381-2>`_.

      
Getting Started (Mac OS X)
===============

It is recommended to run **pyeb** in a virtual environment thus it
will not have collateral effects on your local installation. **pyeb**
dependencies are the Z3 solver, antlr Python runtime, and the antlr
tools. 

1.  Creating and activating the virtual environment::

      python -m venv .venv
	  
      source .venv/bin/activate 

      Optionally, you can deactivate the virtual environment  after
      using **pyeb**::

      deactivate
      
2.  Installing dependencies::
      
      pip install z3-solver==4.13.0.0

      pip install antlr4-tools==0.2.1

      pip install antlr4-python3-runtime==4.13.1
      

3.  Installing **pyeb**::
      
      pip install pyeb

      
Command Line Usage (Mac OS)
==================

1. Running **pyeb**::

    **pyeb** <python-file>


    We have included a **sample** folder with several object-oriented
    examples of sequential algorithms (binary search, squared root, inverse function, etc.)::

      **pyeb** sample/binsearch_oo.py

      
Unit testing with **pytest**
===================================

1. Installing **pytest**::

   pip install **pytest**

2. Running **pytest** on a file in the **sample** directory::

     **pytest** tests/test_binsearch.py


GitHub Installation 
===================================

You might want to install and run the latest version of **pyeb** available from GitHub.

1.  Installing **pyeb**::
      
      mkdir dist
      
      cd dist

      git init

      git remote add origin https://github.com/ncatanoc/pyeb.git

      git pull origin main
      
      git branch -M main

2.  Running **pyeb** as a console script::
      
      python main.py sample/binsearch_oo.py

3.  Optionally,  Running **pyeb** as a module::
      
      python -m pyeb sample/binsearch_oo.py

   
Troubleshooting
=======================

For any questions or issues regarding **pyeb**, contact Nestor Catano [nestor.catano@gmail.com](mailto:nestor.catano@gmail.com).

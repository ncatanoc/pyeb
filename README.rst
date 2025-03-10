**pyeb** is a Python implementation of `Event-B's refinement calculus <(https://www.amazon.com/Modeling-Event-B-Jean-Raymond-Abrial-ebook/dp/B00AKE1X6G/ref=sr_1_1?crid=Z3EK47C5ZPF8&dib=eyJ2IjoiMSJ9.y0_vyeR7jV-Oj4yF28ueHqqWE4mUkUqg81kXg-hMs97kgOTibmPyedfD24D51HmTqaXOd2JLhxAksYcjCpzp-IUu_2AAJKqzVyfaQLYmIE7b4gSU4d10tXBra1KZDW39byq9804lBnqJWuDMmKzue46_K8qDg29UojbXh3SJDB_NZ8dJNo5ahtap-gjsQmm4x2BLPLaRx2tg27MV4kFiJ31vRq_UyuN0f228qOM8tVE.Bd9FAFBQWGvOHRObi6YOT0L772WFbXVPzFKBFbTY3wM&dib_tag=se&keywords=abrial&qid=1712764662&s=books&sprefix=abrial%2Cstripbooks-intl-ship%2C240&sr=1-1>`_. It takes an Event-B model as
an input and generates proof-obligations that are eventually discharged with the Z3 SMT
solver. Event-B models are written in Python following a special Object-Oriented syntax and
notation. The **pyeb** tool generates proof obligations such as invariant preservation, feasibility
of non-deterministic event actions, guard strengthening, simulation, preservation of machine
variants, among others.  **pyeb** uses `Z3 Python API <https://github.com/Z3Prover/z3>`_ to discharge the `proof obligations <http://deploy-eprints.ecs.soton.ac.uk/122/1/sld.ch15,seq.pdf>`_ 
automatically. It supports large parts of Event-B' syntax such as non-deterministic assignments,
events, machines, contexts, and machine refinements. 

As future work, we plan to support code generation for **pyeb** models into Python and Rust
programming languages. Our future work on code generation will focus on two axes: *(i.)* we plan to
generate code for sequential programs as described by J.-R. Abrial, and *(ii.)* we plan
to generate code for concurrent reactive systems similar to the
approach followed by the EventB2Java tool.

      
Getting Started (Mac OS X)
===============

It is recommended to run **pyeb** in a virtual environment thus it
will not have collateral effects on your local installation. **pyeb**
dependencies are the Z3 solver, antlr Python runtime, and the antlr
tools. 

1.  Creating and activating the virtual environment::

      python -m venv .venv
	  
      source .venv/bin/activate 

2. Optionally, you can deactivate the virtual environment  after
      using **pyeb**::

	deactivate
      
3.  Installing dependencies::
      
      pip install z3-solver==4.13.0.0

      pip install antlr4-tools==0.2.1

      pip install antlr4-python3-runtime==4.13.1
      

4.  Installing **pyeb**::
      
      pip install pyeb

      
Command Line Usage (Mac OS)
==================

1. Running **pyeb**::

     pyeb python-file

2. We have included a **sample** folder with several object-oriented
   examples of sequential algorithms (binary search, squared root,
   inverse function, etc.)::

     pyeb sample/binsearch_oo.py

      
Unit testing with **pytest**
===================================

1. Installing **pytest**::

     pip install pytest

2. Running **pytest** on a file in the **sample** directory::

     pytest tests/test_binsearch.py


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

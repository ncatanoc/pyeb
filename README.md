**pyeb** is a Python implementation of
[Event-B's refinement calculus](https://www.amazon.com/Modeling-Event-B-Jean-Raymond-Abrial-ebook/dp/B00AKE1X6G/ref=sr_1_1?crid=Z3EK47C5ZPF8&dib=eyJ2IjoiMSJ9.y0_vyeR7jV-Oj4yF28ueHqqWE4mUkUqg81kXg-hMs97kgOTibmPyedfD24D51HmTqaXOd2JLhxAksYcjCpzp-IUu_2AAJKqzVyfaQLYmIE7b4gSU4d10tXBra1KZDW39byq9804lBnqJWuDMmKzue46_K8qDg29UojbXh3SJDB_NZ8dJNo5ahtap-gjsQmm4x2BLPLaRx2tg27MV4kFiJ31vRq_UyuN0f228qOM8tVE.Bd9FAFBQWGvOHRObi6YOT0L772WFbXVPzFKBFbTY3wM&dib_tag=se&keywords=abrial&qid=1712764662&s=books&sprefix=abrial%2Cstripbooks-intl-ship%2C240&sr=1-1). It takes an Event-B model as an input and generates proof-obligations that are eventually discharged with the Z3 SMT solver. Event-B models are written in Python following a special Object-Oriented syntax and notation. The **pyeb** tool generates proof obligations such as invariant preservation, feasibility of non-deterministic event actions, guard strengthening, simulation, preservation of machine variants, among others.  **pyeb** uses [Z3's Python API](https://z3prover.github.io/api/html/namespacez3py.html) to discharge the proof obligations automatically. It supports large parts of Event-B' syntax such as non-deterministic assignments, events, machines, contexts, and machine refinements.

As future work, we plan to support code generation for **pyeb** models into Python and Rust programming languages. Our future work on code generation will focus on two axes: *(i.)* we plan to generate code for sequential programs as described by J.-R. Abrial [here](https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/122/), and *(ii.)* we plan to generate code for concurrent reactive systems similar to the approach followed by the [EventB2Java tool](https://link.springer.com/article/10.1007/s10009-015-0381-2).


Dependencies (Mac OS X)
===================================

We are currently using version 4.13.0.0 of Z3's Python API.

1.  Installing the z3-solver::
      
      python3 -m pip install z3-solver

      
Getting Started
===============

It is recommended to run **pyeb** in a virtual environment thus it will not have collateral effects on your local installation. 

1.  Creating and activating the virtual environment::
      
      python3 -m venv <DIR>
	  
      source <DIR>/bin/activate

2.  Installing **pyeb**::
      
      pip install --index-url https://test.pypi.org/simple/ pyeb

3.  Running **pyeb**::

	**pyeb** path-to-file.py

	We have included a **sample** folder with several object-oriented
examples of sequential algorithms (binary search, squared root,
inverse function, etc.) whose original Event-B models have written by J.-R. Abrial.
      
      **pyeb** sample/sqrt_oo.py

4.  Optionally, you might want to deactivate your virtual environment
    after having used **pyeb**::
      
      deactivate


GitHub Installation and pytest
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
      
      python main.py path-to-file.py

3.  Optionally,  Running **pyeb** as a module::
      
      python -m pyeb <tests.sqrt>

4.  Optionally,  Running **pyeb** with **pytest**::
      
      **pytest** path-to-file.py

   
Troubleshooting
=======================

For any questions or issues regarding **pyeb**, contact Nestor Catano [nestor.catano@gmail.com](mailto:nestor.catano@gmail.com).

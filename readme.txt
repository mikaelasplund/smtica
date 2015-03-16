SMTICA v.0.2

This repository contains the formal model of a vehicular coordination
system, where multiple vehicles arbitrate access to shared
resources. The model includes a specific scenario with a single
intersection and a coordination protocol CwoRIS. 

A description of this system has been submitted to the IEEE
Transactions on Intelligent Transportation System. 

Version history:
*******************************************************
v0.1 - Simple model using smtlib notation, described in FM12 paper
v0.2 - More general model submitted for publication

Files:
*******************************************************
basictypes.py		-	basic definitions
communication.py  	- 	model of communication
environment.py  	- 	model of the physical environment
helpers.py         	-	mathematical helper functions
otherentities.py 	- 	model of other entities 
printing.py  		- 	used for printing to console
progress.py  		- 	constraints necessary when verifying progress
prover.py       	- 	functions used to prove system properties
readme.txt		- 	this file
resourceenv.py  	- 	interface between resources and physical model
resources.py		- 	model of resources
safety.py  		- 	invariants
statemachine.py  	- 	subject vehicle automaton
successor.py  		- 	contains the successor function
validate.py             - 	functions to validate model against simulation
variables.py     	-	basic variables
verify-from-params.py	- 	main file for verifying safety and progress

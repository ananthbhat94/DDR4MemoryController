# DDR4MemoryController
HDL code for a DDR4 memory controller implementing an Open Page Policy and Out of Order execution.
This project doesnt have an extensive testbench. However a Top module is included with 4 Write commands.
This project was originally developed for the emulator. It has however been modified to run on a simulator.
QuestaSim has been used as a simulator 
Authors:  Ananth Bhat
          Niraj Thakkar
          Sriram VB
          Shivank Dhote

A make file has been provided. To run the project:
% make
This will automatically create a library, compile the files and simulate the project.
The make file has been created with respect to QuestaSim.

The authors of each file are listed below:
Ananth Bhat: MemoryController.sv, DDR4Interface.sv, ReadWrite.sv, ShiftReg.sv,C2MInterface.sv
Sriram VB:  Scheduler.sv, DDR4Interface.sv, ReadWrite.sv, ShiftReg.sv,Memory.sv,CalcMax.sv
Niraj Thakkar: Read_data_comm.sv, Receive_command.sv, Send_command.sv
Shivank Dhote: Top.sv

The description of each file is given at the top of each file.

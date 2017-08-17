## DDR4MemoryController

#### Introduction

This project implements a DDR4 Memory Controller in SystemVerilog which implements Open Page Policy and Out of Order execution.
The project includes a CacheBFM (integrated in the Top Module) and a Memory BFM. The cache controller sends 64 bytes of write-data along with a 32-bit address and a read/write request. The memory controller has a queue which can store up to 8 requests. 
This project doesnt include an extensive testbench. However a Top module is included with 4 Write commands. The top module can be replaced with a more exhastive testbench.
This project was originally developed for the Veloce Emulator. It has however been modified to run on the QuestaSim simulator.

Authors:  

          Ananth Bhat
          
          Niraj Thakkar 
          
          Sriram VB    
          
          Shivank Dhote
          
#### Steps for Simulation

A make file has been provided. To run the project, make sure QuestaSim is installed. In the Direcotry, run the following command:

>% make

This will automatically create a library, compile the files and simulate the project.
The make file has been created with respect to QuestaSim.


#### The contribution of each memeber is given below:

Ananth Bhat: MemoryController.sv, DDR4Interface.sv, ReadWrite.sv, ShiftReg.sv,C2MInterface.sv

Sriram VB:  Scheduler.sv, DDR4Interface.sv, ReadWrite.sv, ShiftReg.sv,Memory.sv,CalcMax.sv

Niraj Thakkar: Read_data_comm.sv, Receive_command.sv, Send_command.sv

Shivank Dhote: Top.sv

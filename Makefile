ll: clean compile sim

RTL=	C2MInterface.sv \
		DDR4Interface.sv \
		Memory.sv \
		Receive_command.sv \
		Scheduler.sv \
		Controller_FSM.sv \
		Timer.sv \
		CalcMax.sv \
		MemoryController.sv \
		ReadWrite.sv \
		Read_data_comm.sv \
		Send_command.sv \
		ShiftReg.sv \
		Top.sv

TOP=	Top

run: work compile sim

work:
	vlib work
compile:
	vlog -source ${RTL}
sim:
	vsim -c ${TOP} -do "run -all;"
clean:
	rm -rf work transcript vsim.wlf

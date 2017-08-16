//This file contains the Memory BFM which interacts with the Mrmroy Controller.
//Author: Sriram VB

`define DPRINT //$display($time, "\t%m\tState: %s",State.name)

module Memory#(`include "Definitions.pkg")(DDR4Interface.Memory Bus, input clock2x);
	
	// Memory
	logic [DATAWIDTH - 1:0] Mem [logic[31:0]];
	
	//Local Bank and Bankgroup variables
	logic [BWIDTH-1:0] Bank;
	logic [BGWIDTH-1:0] BankGrp;
	
	// Register Array and  pointers 
	logic [TCL-1:0][ADDRESSWIDTH-1:0] AddressReg; //Array to store addresses
	wire  [ADDRESSWIDTH - 1:0] Address;//Address given by the FSM to perform data transfer
	logic [SHIFTBITS-1:0] Ptr,LatchPtr; //Pointers to access AddressReg. Latch pointer latches Ptr during data transfer
	logic [4:0] WaitRegR;
	logic [3:0] WaitRegW;//Registers used to wait during data transfer
	
	wire [BANKS*BANKGROUP-1:0] Rarray,Warray;//Array of reads and writes respectively	
	logic W,R;	//W,R are the OR of Warray and Rarray Respectively
	logic [BANKS*BANKGROUP-1:0] Select; //Selects which FSM is active
	
	wire StartRn, StartWn; //Enable signals for the Read and Write modules
	wire Start_check; //checks validity of enable signals for read and write modules
	
	// Scheduled read writes
	logic [SHIFTBITS:0]RSch,WSch;//Output of Shift Register which waits for TCL
	logic [ADDRESSWIDTH-1:0] MemAddress;//Stores the effective address for Memory Access
	
	//Data wire is defined to store the incoming data from the controller
	//into memory array
	wire [DATAWIDTH-1:0] Data;
	logic [DATAWIDTH-1:0] Data_var;

	//Continuous Assigns
	assign 	{Bank,BankGrp} = {Bus.b,Bus.bg};
	assign {W,R} = {|Warray,|Rarray};
	assign StartRn = ~|WaitRegR;
	assign StartWn = ~|WaitRegW;
	assign Start_check = StartRn & StartWn;
	assign Data = Data_var;

	//Logic to Handle the pointer to the address register
	always_ff@(posedge Bus.clock) 
	begin
	if(!Bus.reset_n)
			Ptr <= '0;
	else if(W || R)
			Ptr <= Ptr + 1'b1;
	else
			Ptr <= Ptr;
	end
	
	//Logic to handle Latchpointer and memory address
	always_latch begin
		if(!Bus.reset_n)
			MemAddress = '0;
		else if(WSch[SHIFTBITS]) begin
			LatchPtr = WSch[SHIFTBITS-1:0];
			MemAddress = AddressReg[LatchPtr];
		end
		else if(RSch[SHIFTBITS]) begin
			LatchPtr = RSch[SHIFTBITS-1:0];
			MemAddress = AddressReg[LatchPtr];
		end
	end

	//Always Assign the incoming address from FSM into the Address Register
	always_latch 
			AddressReg[Ptr] = Address;

	//Logic to Handle Wait registers 
	always_ff @(posedge Bus.clock)  begin
		if(!Bus.reset_n) begin
			WaitRegW <= '0;
			WaitRegR <= '0; 
		end
		else begin 
			WaitRegW <= {WSch[SHIFTBITS], WaitRegW[3:1]};//Shift Registers
			WaitRegR <= {RSch[SHIFTBITS], WaitRegR[4:1]};
			//Assertions to check that atmost there is only 1 bit which is 1
			//and there are no unknowns in the registers
			assert( !$isunknown(WaitRegW) && $countones(WaitRegW)<=1)
				else $fatal("WaitRegW value isnt perfect\tWaitRegW:%b",WaitRegW);
			assert(!$isunknown(WaitRegR) && $countones(WaitRegR)<=1)
				else $fatal("WaitRegR value isnt perfect\tWaitRegR:%b",WaitRegR);
		end
	end
	
	always_latch  begin
		if(!StartRn) begin 
			Mem[MemAddress] = Data;
		end
		else if(!StartWn)
			Data_var = Mem[MemAddress];
		else begin
			Data_var = 'z;
		end
	end
	
	always_latch begin
		if (!W) 
			Bus.dq_m = 'z;
	end

//////////////////////////INSTANTIATIONS///////////////////////////////////////

	//Instantiate the FSM Array using a Generate loop
	genvar i;
	generate;
	for(i=0;i<(BANKS*BANKGROUP);i++) begin
		assign Select[i] = (i=={BankGrp,Bank});//Select logic
		MemoryFSM fi(Bus,Select[i],Address,Warray[i],Rarray[i]);
	end
	endgenerate
	
	//Instantiate the read and write modules 
	ReadMod RM(	.read(~StartRn),
				.reset(StartRn),
				.DataBus(Bus.pin_dq),
				.DataHost(Data),
				.DQS_t(Bus.dqs_t),
				.DQS_c(Bus.dqs_c)
				);
				
	WriteMod WM(.clock2x(clock2x),
				.reset(StartWn),
				.write(~StartWn),
				.DataBus(Bus.pin_dq),
				.DataHost(Data),
				.DQS_t(Bus.dqs_t),
				.DQS_c(Bus.dqs_c)
				);

	
	//Instantiate the 2 shift registers to wait for TCL. One is for read and
	//the other is for write
	ShiftRegMem r(Bus.clock,~Bus.reset_n,{R,Ptr},RSch);
	ShiftRegMem w(Bus.clock,~Bus.reset_n,{W,Ptr},WSch);

////////////////////////////////////////////////////////////////////////////////

//Final block displays memory contents
final begin
	foreach(Mem[i]) begin
		$display("Mem[%x] = %x",i,Mem[i]);
	end
end

//////////////////////////CONTINUOUS ASSERTIONS///////////////////////////////////////////////////////
	//LatchPointer should remain constant for 4 clock cycles

	property Latch_Pointer;
		@(posedge Bus.clock)
			(RSch[SHIFTBITS] || WSch[SHIFTBITS])|=> !($changed(LatchPtr))[*3];
	endproperty

	assert property (Latch_Pointer)
		else $fatal("Latch pointer not constant\tLatchPointer:%0d",LatchPtr);


	property RWReg_Check;
		@ (posedge Bus.clock)
			($fell(StartRn) || $fell(StartWn)) |-> !Start_check[*3];
	endproperty

	assert property (RWReg_Check)
		else $fatal("Both Read and Write modules are active. StartWn:%x\tStartRn:%x",StartWn,StartRn);


	property Read_To_Start;
		@(posedge Bus.clock)
			$rose(R) |-> ##(TCL-2) $rose(RSch[SHIFTBITS]);
	endproperty
	assert property (Read_To_Start)
		else $error("TCL violation in Memory");

	property Start;
		@ (posedge Bus.clock)
			$fell(StartRn) |=> !$changed(StartRn)[*3];
	endproperty

	assert property (Start)
		else $error("Start is not Low for 4 clock cycle");

//////////////////////////////////////////////////////////////////////////////////////////////////


endmodule


/*****************************************************************************************
// MEMORY FSM for each BANK and BANK GROUP 
******************************************************************************************/
module MemoryFSM#(`include "Definitions.pkg")
(
	interface Bus,
	input bit Select,
	output logic [ADDRESSWIDTH-1:0]Address,
	output logic W,R
);
	wire Activate;
	logic [RWIDTH - 1:0]	Row;
	logic [CWIDTH - 1:0]	Column;
	logic [B_BITS- 1:0]		Bank;
	logic [BG_BITS- 1:0]	BankGrp;

	typedef enum{init, wait_state, idle, refresh, activate, read, write, readA, writeA, precharge}State_T;	
	State_T State, Prev;

	// Next State Logic for States activate, read, write
	function automatic State_T ReadWriteState(bit IsWrite, IsRead, IsWriteA, IsReadA, IsPrePreA);
		State_T next;
		unique case({IsWrite, IsRead, IsWriteA, IsReadA, IsPrePreA})
			5'b10000: next = write;	
			5'b01000: next = read;	
			5'b00100: next = writeA;	
			5'b00010: next = readA;	
			5'b00001: next = precharge;
			5'b00000: next = wait_state;	
		endcase	
		return next;
	endfunction

	// Next State Logic in Sequential Block
	always_ff@(posedge Bus.clock)
	begin
		if(!Bus.reset_n)
			State <= init;
		else if(Select)
			unique case(State)	
			init	: begin
						unique case({Bus.IsActivate, Bus.IsRefresh})
						2'b10: State <= activate;
						2'b01: State <= refresh;
						2'b00: State <= idle;
						endcase 
					  end

			idle	: begin
						unique case({Bus.IsActivate, Bus.IsRefresh})
						2'b10: State <= activate;
						2'b01: State <= refresh;
						2'b00: State <= idle;
						endcase 
					end
					// put assertion for read and write signals to be 0 here
					/*idle_S: assert ($onehot0({Bus.IsActivate, Bus.IsRefresh})
					else 
						$warning("Idle State: Activate- %b, Refresh-%b", $sample(Bus.IsActivate), $sample(Bus.Refresh));*/
			refresh	: State <= idle;
			activate: State <= ReadWriteState(Bus.IsWrite, Bus.IsRead, Bus.IsWriteA, Bus.IsReadA, Bus.IsPrePreA);
			write	: State <= wait_state;
			writeA	: State <= precharge;
			read	: State <= wait_state;
			readA	: State <= precharge;
			wait_state:State <= ReadWriteState(Bus.IsWrite, Bus.IsRead, Bus.IsWriteA, Bus.IsReadA, Bus.IsPrePreA);
			precharge: State <= idle;
			endcase
		else
			State <= State;
	end

	// Output Function Logic
	always_comb
	begin
		{W,R} = '0;
		Address = 'z;
		unique case(State)
			init	: `DPRINT;
			idle	: `DPRINT;
			refresh	: `DPRINT;
			activate: begin
						`DPRINT;
						{Row, Bank, BankGrp} = Bus.ReadRowBank;
					end
			read,readA	: begin
							`DPRINT;
							{Column, Bank, BankGrp} = Bus.ReadColumnBank;
							Address = CalcAddress(Row, Bank, BankGrp, Column);
							W = 1'b1;
						end
			write,writeA	: begin
								`DPRINT;
								{Column, Bank, BankGrp} = Bus.ReadColumnBank;
								Address = CalcAddress(Row, Bank, BankGrp, Column);
								R = 1'b1;
							  end
			wait_state:	`DPRINT;
			precharge:	`DPRINT;
		endcase
	end

	function automatic logic [RWIDTH + Bus.B_BITS + Bus.BG_BITS + CWIDTH + 3 - 1:0] CalcAddress(logic[RWIDTH-1:0] Row, logic[Bus.B_BITS-1:0]Bank, logic[Bus.BG_BITS-1:0]BankGrp,logic [CWIDTH-1:0]Column);
		logic [ADDRESSWIDTH-1:0]	Address;
		Address = {Row, Bank, Column[CWIDTH-1:3],BankGrp,6'b000_000};
		return Address;

	endfunction

endmodule


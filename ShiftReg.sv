//This file contains shift registers used to implement synthesizable delays
//The modules are used in both the controller and the memory
//ShiftRegMC is used by the memory controller and ShiftRegMem is used by the memory
//Authors: 	Ananth Bhat
//			Sriram VB
module ShiftRegMC#(`include "Definitions.pkg")
(
	input clock, reset,
	input [SHIFTBITS:0]ShiftInput,
	output wire [SHIFTBITS:0]ShiftOutput
);

logic [TCL-2:0][SHIFTBITS:0]ShiftMem;

always_ff@(posedge clock) begin
	if(reset)
		ShiftMem <= '0;
	else begin
		ShiftMem <= {ShiftInput, ShiftMem[TCL-2:1]};
		assert(!$isunknown(ShiftInput))
			else $fatal("Input to be Shifted contains unknown bits\tWaitRegWr:%x",ShiftInput);
		end
end

assign ShiftOutput = ShiftMem[0];
endmodule


module ShiftRegMem#(`include "Definitions.pkg")
(
	input clock, reset,
	input [SHIFTBITS:0]ShiftInput,
	output wire [SHIFTBITS:0]ShiftOutput
);

logic [TCL-3:0][SHIFTBITS:0]ShiftMem;

always_ff@(posedge clock) begin
	if(reset)
		ShiftMem <= '0;
	else begin
		ShiftMem <= {ShiftInput, ShiftMem[TCL-3:1]};
		assert(!$isunknown(ShiftInput))
			else $fatal("Input to be Shifted contains unknown bits\tWaitRegWr:%x",ShiftInput);
		end
end

assign ShiftOutput = ShiftMem[0];
endmodule

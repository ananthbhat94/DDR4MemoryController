//This is a Data transfer module between the Memory Controller and the Memory. 
//It facilitates Data Transfer at Double Data Rate(DDR)
//The modules in this file are used by both the Memory and the Controller
//Authors: 	Ananth Bhat
//			Sriram VB

////////////////////////////////////DATA TRANSFER MODULE///////////////////////////////////
//Print Definition
/***********Read Module********************/
//Reads 8 bursts of data from the Bus to the Host.
//This module is used both by the Memory COntroller and the Memory BFM
module ReadMod(
	input read,
	input reset,
	input [63:0] DataBus,
	output [7:0][63:0] DataHost,
	input DQS_t,
	input DQS_c);

//Variable Definitions
logic [7:0][63:0] varDataHost;
assign DataHost = varDataHost;
logic [2:0] count;

//Counter to count 8 bursts of Data
always_ff @(posedge DQS_t, posedge DQS_c)
begin
	if(reset)
		count <= 3'b0;
	else 
		count <= count + 1'b1;
end

//Procedural Block to transfer data
always_ff @(posedge DQS_t, posedge DQS_c) begin
	if(reset) begin
		varDataHost <= 'z;
	end
	else if(read) begin
		varDataHost[count] <= DataBus;
		$strobe($time,"\t%m\tREAD\tDataBus is:%x\tDataHost is:%x\tcount=%0d",DataBus,DataHost,count); 
		$display($time,"\t%m\tcount=%0d",count);
	end
	else begin
		varDataHost <= 'z;
	end
end

endmodule


/***********Write Module********************/
//Writes 8 bursts of data from the Host to the Bus.
//This module is used both by the Memory COntroller and the Memory BFM
module WriteMod(
	input clock2x,
	input reset,
	input write,
	output [63:0] DataBus,
	input [7:0][63:0] DataHost,
	output logic DQS_t,
	output logic DQS_c);

//Variable Definition
logic [63:0] varDataBus;
logic [2:0] count;

assign DataBus = varDataBus;

//Counter to count 8 bursts of Data
always_ff @(posedge clock2x)
begin
	if(reset)
		count <= 3'b0;
	else 
		count <= count + 1'b1;
end

//Create Data Synchronous Strobe signals (DQS)
always_ff@(posedge clock2x) begin
	if(reset)
		DQS_t = 1'b1;
	else begin
	case(write)
		1'b0: DQS_t <= 'z; 
		1'b1: DQS_t <= ~DQS_t;
	endcase
	end
end
assign DQS_c = reset?1'b1:~DQS_t;

//Procedural Block to transfer data
always_ff@(negedge clock2x) begin
	if(reset)
		varDataBus <= 'z;
	else if(write)
		begin 
			varDataBus <= DataHost[count];
			$display($time,"\t%m\tcount=%0d",count);
			$strobe($time,"\t%m\tWRITE\tDataHost is:%x\tDataBus is:%x",DataHost[count],DataBus);
		end
	else
		varDataBus <= 'z;
end

endmodule

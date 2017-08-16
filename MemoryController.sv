//This file contains the Memory Controller module.
//The Scheduler is included in another file named Scheduler.sv. This file instantiates
//all necessary modules, such as the scheduler, and the communication module are instantiated here.
// Author: Ananth Bhat

module MemoryController
#(
`include "Definitions.pkg"
)
(
	input logic reset,clock,clock2x,
	interface DDR4Bus, MCTx, MCRx
);

//Define signals for connection between read_command 
logic [ADDRESSWIDTH-1:0] Address_cs,Address_sf;//Scheduler Output
logic [DATAWIDTH-1:0] Data_cs,Data_sf;//Scheduler Output
logic rw_cs,rw_sf;//ReadWrite Cache to Scheduler;ReadWrite Scheduler to FSM
logic [2:0] tag,tagreadin,tagreadout;
logic full; //Full signal between Scheduler and receive_command
logic buff;

//Define Control,Address,data Signals for the FSM
logic start,refresh,ap,done;
wire [DATAWIDTH-1:0] data;
logic [BWIDTH-1:0] bank;
logic [BGWIDTH-1:0] bankgroup;
logic [RWIDTH-1:0] row;
logic [CWIDTH-1:0] column;
logic [1:0] PageHit;
logic PageMiss, PageEmpty;
logic valid;

/////////////////////////BUFFER///////////////////////////////////

//A buffer is created to store the result of a read
//0The upper 512 MSB is the Data, the lower 3 bits are the tag
logic [DATAWIDTH+TWIDTH-1:0] ReadBuffer;
wire [514:3] databuff;
always_ff @(posedge clock)
begin
	if(buff) begin
		ReadBuffer[514:3] <= databuff;
		ReadBuffer[2:0] <= tagreadout;//Put Tag
	end
	else
		ReadBuffer <= ReadBuffer;
end
//////////////////////////////////////////////////////////////////


assign row = Address_sf [31:17];
assign bank = Address_sf[16:15];
assign column = {Address_sf[14:8],Address_sf[5:3]};
assign bankgroup = Address_sf[7:6];

//Instantiate all necessary mdoules
//Instantiate the FSM
MemContFSM m( 	.start, .rw(rw_sf), .refresh, .ap,
		.bank,.bankgroup,
		.row,.column,
		.datawrite(Data_sf), .dataread(databuff), .buff,.tagreadin,.tagreadout,
		.DDR4Bus(DDR4Bus),
		.reset,.clock,.clock2x,.done,
		.PageHit,.PageEmpty,.PageMiss
 	    );

//Instantiate the Scheduler
Scheduler S (	.DataIn(Data_cs),.AddrIn(Address_cs), 
		.rw_in(rw_cs),.reset,.clock,.valid,
		.DataOut(Data_sf), .AddrOut(Address_sf),
		.rw_out(rw_sf),.full,.refresh,.ap,.tag,
		.start,.done,.tagread(tagreadin),.tagfsm(tagreadout),
		.buff,.PageHit,.PageMiss,.PageEmpty
	    );

//Interface to the Memory Controller receiver that receives requests from cache 
receive_command rc (	.IF(MCRx),.data_out(Data_cs), 
			.addr_out(Address_cs), .valid,.rw_out(rw_cs),
			.tag_gen(tag),.fifo_full(full)
		   );

//Interface to the Memory Controller that sends data to cache
send_read_data srd (	.IF(MCTx), 
			.data_in(ReadBuffer[514:3]), 
			.tag_gen(ReadBuffer[2:0]),
			.internal_ready(buff)
		   );

endmodule




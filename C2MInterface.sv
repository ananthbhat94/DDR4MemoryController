//This is the interface between the Cache BFM and the Memory Controller.
//Author: Ananth Bhat

interface C2MInterface
#(
	parameter DWIDTH = 512, AWIDTH = 32
)
(
	input logic clock,reset
);	

////////////////////////////////TRANSACTION SIGNALS//////////////////////////////

logic [DWIDTH-1:0] data_tran; 	//Data sent from Cache to Memory Controller to
								//be written

logic [AWIDTH-1:0] addr;		//Address sent from Cache to Memory Controller 

logic rw;						//Read-Write signal

logic valid_tran;				//Indicates that the Data from Cache to Memory
								//is valid

logic [2:0] tag_tran;			//Tag returned along with acknowledgemnt
								//signal

logic ack_tran;					//Acknowledgement signal from Memory to cache

logic full;						//A full signal indicating that the memory
								//controller cannot accept any more transactions

//////////////////////////////READ DATA SIGNALS//////////////////////////////////////

logic [DWIDTH-1:0] read_data;	//Data sent from Memory to Cache in
								//response to a read
logic [2:0] tag_data;			//Tag sent along with the data from the
								//Memory controller to Cache

logic ack_data;					//Ack sent from Cache to Memory

logic valid_data;				//Indicates that the data sent from Memory
								//to cache is valid


//////////////////////////////////MODPORTS///////////////////////////////////////////

modport Cache_tran	(
						input 	ack_tran,tag_tran,full,reset,clock,
						output  addr, data_tran, rw, valid_tran
					);

modport Cache_data 	(
						input read_data,reset,clock,tag_data,valid_data,
						output ack_data
					);

modport Mem_tran	(
						input clock,reset,addr,data_tran,rw,valid_tran,
						output 	ack_tran,tag_tran,full
					);

modport Mem_data	(
						input ack_data,reset,clock,
						output read_data,tag_data,valid_data						
					);

endinterface

//This module is used by the Memory controller to receive commands from the Cache
//Author: Niraj Thakkar
module receive_command 
(
	C2MInterface.Mem_tran IF,
	input logic fifo_full, [2:0] tag_gen,
	output logic 	rw_out, valid,
					[IF.AWIDTH-1:0] addr_out,
					[IF.DWIDTH-1:0]data_out
);

logic [IF.DWIDTH-1:0] data;
logic [IF.AWIDTH-1:0] addr;
logic [2:0] tag;
logic rw;
logic full;
logic ack;

assign valid = IF.ack_tran;

//Enumerated types of States
typedef enum logic [1:0] {init=2'b01,receive=2'b10}st;
st state,next_state;

//Sequential Logic
always_ff @(posedge IF.clock)
begin
	data_out<=data;
	addr_out<=addr;
	rw_out<=rw;

if(IF.reset)
	state<=init;
else begin
	state<=next_state;
	end
end

//Next State Logic
always_comb
begin
	case(state)
	init:	if(fifo_full || !IF.valid_tran)
				next_state=init;
		 	else
				next_state=receive;
	
	receive: if(fifo_full || IF.valid_tran)
				next_state=init;
			 else
				next_state=receive;
	endcase
end

always_comb
begin
	case(state)
	init:
		begin
		if(fifo_full)
			IF.full=1;
		else
			IF.full=0;
		addr=IF.addr; data=IF.data_tran;
		rw=IF.rw; IF.ack_tran=0;
		tag=tag_gen;
		end
	receive:
		begin
		full=0;
		addr=IF.addr;
		rw=IF.rw;
		IF.ack_tran=1;
		IF.tag_tran=tag_gen;
		data=IF.data_tran;
		end
	endcase
end

endmodule

//This module is used by the Cache BFM to send commands to the Memory Controller
//Author: Niraj Thakkar
`define DPRINT //$display($time, "\t%m\t STATE: %s",state.name)
module send_command (C2MInterface.Cache_tran IF,input logic rw_in,valid_xrtl, [IF.DWIDTH-1:0] data_in,[IF.AWIDTH-1:0] addr_in, output logic ack_xrtl,full_xrtl/*,valid_out*/,[2:0] tag_out);

logic [IF.DWIDTH-1:0] data;
logic [IF.AWIDTH-1:0] addr;
logic [2:0] tag;
logic rw,ack;
logic val;
 
typedef enum logic [1:0] {init=2'b01,send=2'b10}st;
st state,next_state;

//Sequential Logic
always_ff @(posedge IF.clock)
begin
full_xrtl<=IF.full;
IF.data_tran<=data;
IF.addr<=addr;
IF.rw<=rw;
//tag_out<=tag;
ack_xrtl<=ack;
if(IF.reset)
	state<=init;
else
	state<=next_state;
end

//Next State Logic
always_comb
begin
	case(state)
	init:if(IF.full==0 && valid_xrtl==1)
			next_state=send;
		 else
			next_state=init;
	send: 	if(IF.ack_tran)
				next_state=init;
			else 
				next_state=send;
	endcase
end

//Output Function Logic
always_comb
begin
`DPRINT;
	case(state)
	init:
		begin
		addr=addr_in;
		rw=rw_in;
		IF.valid_tran=0;
		ack=0;
		tag=IF.tag_tran;
		data=data_in;
		end
		
	send:
		begin
		addr=addr_in;
		rw=rw_in;
		IF.valid_tran=1; ack=1;
		tag_out=IF.tag_tran;
		data=data_in;
		end
	endcase
end

endmodule


`timescale 1ns/100ps




   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111
   `define add   6'b100000
   `define addu  6'b100001
   `define sub   6'b100010
   `define subu  6'b100011
   `define and   6'b100100
   `define or    6'b100101
   `define xor   6'b100110
   `define nor   6'b100111
   `define slt   6'b101010
   `define sltu  6'b101011
   `define jr    6'b001000
   `define jalr  6'b001001
   `define multu 6'b011001
   `define mfhi  6'b010000
   `define mflo  6'b010010
   `define beq    6'b000100
   `define bne    6'b000101






module multi_cycle_mips(

   input clk,
   input reset,
   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE,start;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;
   reg [2:0] MemtoReg;
   reg [1:0] RegDst,PCsrc;
   reg [31:0] hi,lo;
   // Mux & ALU Control Lines
   reg [2:0] aluOp;
   reg [2:0] aluSelB;
   reg SgnExt, aluSelA, IorD; 
   // Wiring
   wire aluZero,ready;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire [63:0] product;
   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;




   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt ) PC <= #0.1 (PCsrc == 2'b01) ? {PC[31:28], IR[25:0], 2'b00}:(PCsrc == 2'b10) ? A : aluResult;

      if(ready) begin
         hi <= #0.1 product[63:32];
         lo <= #0.1 product[31:0];
      end

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? ((PCsrc == 2'b01) ? {PC[31:28], IR[25:0], 2'b00} : 
                    (PCsrc == 2'b10) ? A : aluResult ): PC;

      if( IRwrt )  IR <= #0.1   mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end
  





   // Sign/Zero Extension
   wire [31:0] SZout = (SgnExt) ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};
         
   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),
      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),
      .WR((RegDst == 2'b01) ? IR[15:11]:(RegDst == 2'b10) ? 5'b11111 : IR[20:16]),
      .WD( (MemtoReg == 3'b000) ? aluResult : (MemtoReg == 3'b001) ? MDR :(MemtoReg == 3'b010) ? SZout:(MemtoReg == 3'b011) ? lo :(MemtoReg == 3'b100) ? hi : (MemtoReg == 3'b101) ? {IR[15:0], 16'h0000} : aluResult)
   );

   






   // ALU-A Mux
   wire [31:0] aluA = (aluSelA) ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      3'b000: aluB = B;
      3'b001: aluB = 32'h4;
      3'b010: aluB = SZout;
      3'b011: aluB = SZout << 2;
      3'b100: aluB = 32'h00000000;
      
   endcase






   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),
      .X( aluResult ),
      .Z( aluZero )
   );

   multiplier_nb_param my_mult(
      .clk(clk),
      .start(start),
      .A(A),
      .B(B),
      .Product(product),
      .ready(ready)
   );
   // Controller Starts Here

   // Controller State Registers
   reg [6:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_J = 5, EX_JAL = 6,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_JR = 9, EX_JALR = 10,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_MFHI = 16, EX_MFLO = 17,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_LUI = 24,
      EX_BRA_1 = 25, EX_BRA_2 = 26,
      // //32 clocks for multiplier 
       EX_ALU_MULT_1 =  27,
       EX_ALU_MULT_2 =  28,
     //additinal state for jump
      EX_jrj=60;

initial

begin
      $display("######################################################");
      $display("######################################################");
		$display("######################################################");
		$display("Meysam Asadi  and  Ilia Hashemirad 99101116  99102456 ");
      $display("######################################################");
      $display("######################################################");
      $display("######################################################");
end










   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;

      PCwrt = 0;           
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      start = 0;
      PCsrc = 2'b00;
      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;     //aluA=PC
            aluSelB = 3'b001;//aluB=4
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            //$display("decode");
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000000: 
               begin  
                  case( IR[5:3] )

                     3'b000: nxt_state = EX_ALU_R; // sll, srl 
                     
                     3'b001: 
                     begin // jr, jalr
                        case(IR[2:0])
                           3'b000: begin // jr
                              nxt_state = EX_JR;
                           end
                           3'b001: begin // jalr
                              nxt_state = EX_JALR;
                           end
                        endcase
                     end
                     3'b010: 
                     begin 
                        case(IR[2:0])
                           3'b000: begin // mfhi
                              nxt_state = EX_MFHI; 
                           end
                           3'b010: begin // mflo
                               nxt_state = EX_MFLO; 
                           end
                        endcase
                     end 
                     3'b011: nxt_state = EX_ALU_MULT_1; // multu
                     3'b100: nxt_state = EX_ALU_R; // add, addu, sub, subu, and, or, xor, nor
                     3'b101: nxt_state = EX_ALU_R; // slt, sltu   
                     3'b110: ;
                     3'b111: ;
                  endcase
               end


               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;          

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
                  
               6'b000_010: nxt_state = EX_J;            // j
               6'b000_011: nxt_state = EX_JAL;          //jal
               6'b001_111: nxt_state = EX_LUI;          // lui
               default: PrepareFetch;
            endcase
         end

         EX_ALU_R: 
         begin
            aluSelA = 1;      //aluA = A
            aluSelB = 3'b000;//aluB = B
            case ( IR[5:0] )
               `add:  aluOp = `ADD;
               `addu: aluOp = `ADD;
               `sub:  aluOp = `SUB;
               `subu: aluOp = `SUB;
               `and:  aluOp = `AND;
               `or:   aluOp = `OR;
               `xor:  aluOp = `XOR;
               `nor:  aluOp = `NOR;
               `slt:  aluOp = `SLT;
               `sltu: aluOp = `SLTU;

               default: 
                  aluOp = 3'bxxx;       
            endcase
            aluSelA = 1;//aluA = A
            aluSelB = 3'b000;//aluB = B
            RegDst = 2'b01;
            MemtoReg = 3'b000;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_ALU_I: 
         begin
           
            case ( IR[28:26] )                           
               3'b000: begin
                  aluOp = `ADD;     //addi
                  SgnExt = 1;
               end
               
               3'b001: begin
                  aluOp = `ADD;     //addiu
                  SgnExt = 0;        
               end     
               3'b010: begin
                  aluOp = `SLT;     //slti
                  SgnExt = 1;
               end   
               3'b011: begin
                  aluOp = `SLTU;     //sltiu
                  SgnExt = 0;
               end   
               3'b100: begin
                  aluOp = `AND;     //andi
                  SgnExt = 0;
               end        
               3'b101: begin
                  aluOp = `OR;     //ori
                  SgnExt = 0;
               end   
               3'b110: begin
                  aluOp = `XOR;     //xori
                  SgnExt = 0;
               end   
               default: aluOp = 3'bxxx;     
            endcase
            aluSelA = 1;//aluA = A
            aluSelB = 3'b010; //aluB = SZout
            RegDst = 2'b00;
            MemtoReg = 3'b000;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_LW_1: begin
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            IorD = 1;        
            MARwrt = 1;
            setMRE = 1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            clrMRE = 1;
            MDRwrt = 1;        
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 2'b00;
            MemtoReg = 3'b001;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_SW_1: begin
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 3'b010;
            aluOp = `ADD;
            IorD = 1;         
            MARwrt = 1;
            setMWE = 1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin             
            aluSelA = 1'b1;
            aluSelB = 2'b000;
            aluOp = `SUB;
            case( IR[31:26] )
               `beq: begin
                  if(aluZero)
                     nxt_state = EX_BRA_2;
                  else
                     PrepareFetch;
               end
               `bne: begin
                  if(!aluZero)
                     nxt_state = EX_BRA_2;
                  else
                     PrepareFetch;
               end
               default: PrepareFetch;
            endcase
         end

         EX_BRA_2: begin  
            PCsrc = 2'b00;     
            SgnExt = 1;
            aluSelA = 0;
            aluSelB = 3'b011;
            PCwrt = 1;
            aluOp = `ADD;
            IorD = 1; 
            MARwrt = 1;
            setMRE = 1;
            nxt_state = FETCH1;
         end

         EX_J: begin        
            PCsrc = 2'b01;
            PCwrt = 1;
            IorD = 1;
				MARwrt = 1;
				setMRE = 1;
            nxt_state = EX_jrj;
         end

         EX_JAL: begin        
            PCsrc = 2'b01;
            PCwrt = 1;
            MemtoReg = 3'b000;
            RegDst = 2'b10;
            RFwrt = 1;
            aluSelA = 0;
            aluSelB = 3'b100;
            aluOp = `ADD;
            IorD = 1;
				setMRE = 1;
				MARwrt = 1;
            nxt_state =EX_jrj ;
         end

         EX_jrj: 
         begin
            PrepareFetch;
         end


         EX_LUI: begin
            MemtoReg = 3'b101;
            RegDst = 2'b00;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_JR: begin         
            PCsrc = 2'b10;
            PCwrt = 1;
            IorD = 1;
				setMRE = 1;
				MARwrt = 1;
            nxt_state =EX_jrj;
         end

         EX_JALR: begin         
            PCsrc = 2'b10;
            PCwrt = 1;
            aluSelA = 0;
            aluSelB = 3'b100;
            aluOp = `ADD;
            MemtoReg = 3'b000;
            RegDst = 2'b10;
            RFwrt = 1;
            IorD = 1;
				setMRE = 1;
				MARwrt = 1;
            nxt_state =EX_jrj;
         end

         EX_ALU_MULT_1: 
         //stay in this state until the product is ready
         begin
            start = 1;
            nxt_state = EX_ALU_MULT_2;       
         end

          EX_ALU_MULT_2: 
          begin
            start = 0;
            if(~ready)
               nxt_state = EX_ALU_MULT_2;
            else 
            begin
               PrepareFetch;
            end
         end
         EX_MFHI: begin
            RegDst = 2'b01;
            MemtoReg = 3'b100;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_MFLO: begin
            RegDst = 2'b01;
            MemtoReg = 3'b011;
            RFwrt = 1;
            PrepareFetch;
         end

         default: PrepareFetch;
      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);

   wire sub = Op != `ADD;

   wire [31:0] bb = sub ? ~B : B;

   wire [32:0] sum = A + bb + sub;

   wire sltu = ! sum[32];

   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

module multiplier_nb_param
#(
     parameter integer nb = 32
  )
(
   //-----------------------Port directions and deceleration
      input clk,  
      input start,
      input [nb-1:0] A, 
      input [nb-1:0] B, 
      output reg [2*nb-1:0] Product,
      output ready
      );
   //------------------------------------------------------

   //----------------------------------- register deceleration
   reg [nb:0] Multiplicand ;
   reg [$clog2(nb):0]  counter;
   //-------------------------------------------------------

   //------------------------------------- wire deceleration
   wire product_write_enable;
   wire [2*nb:0] adder_output;
   //---------------------------------------------------------

   //-------------------------------------- combinational logic
   assign adder_output = (product_write_enable ? Multiplicand : (nb+1)'('b0)) + Product[2*nb-1:nb];
   assign product_write_enable = Product[0];
   assign ready = counter[$clog2(nb)];
   //---------------------------------------------------------

   //--------------------------------------- sequential Logic
   always @ (posedge clk)

      if(start) begin
         counter <= ($clog2(nb))'('b0) ;
         Product <= {(nb)'('b0), B};
         Multiplicand <= A;
      end

      else if(! ready) begin
            counter <= counter + 1;
            Product <= {adder_output, Product[nb-1:1]};
      end   

endmodule


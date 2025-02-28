chapter AFP 

session IsaBIL = Eisbach +
  description "
    IsaBIL: Binary Analysis in Isabelle/HOL using CMU's BAP Intermediary Language.
  "
  options [document = pdf, document_output = "output"]
  sessions
    "Eisbach-Match-Schematics"
    "HOL-ex" (* TODO *)
  directories
    Prelims
    Parser
    OperationalSemantics
    ExpressionSemantics
    StatementSemantics
    Typing
  theories 
    IsaBIL

session "IsaBIL-Ex" in extras = IsaBIL +  
  options [document = pdf, document_output = "output"]
  theories 
    Simp_PC
    Simp_Word
    Simp_Variables
    Mem16
    Mem16_Intros
    Mem16_Elims
    Mem32
    Mem32_Intros
    Mem32_Elims
    Mem64
    Mem64_Intros
    Mem64_Elims

session "IsaBIL-RiscV-64" in "asms/riscv64" = "IsaBIL-Ex" +  
  options [document = pdf, document_output = "output"]
  theories
    RiscV_64
    RiscV_Instructions
    RiscV_Instruction_Intros
    RiscV_Instruction_Elims
    
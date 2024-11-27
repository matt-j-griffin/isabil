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

session "IsaBIL-RiscV-64" in "asms/riscv64" = "IsaBIL-Ex" +  
  options [document = pdf, document_output = "output"]
  theories
    RiscV_64
    
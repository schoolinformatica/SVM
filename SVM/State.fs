module State

open SVMAST

type State = 
  {
    PC : int
    ProgramArea : Program
    Memory : Literal list
    Register : Map<Register, Literal>
    Labels : Map<string, Position>
  }

  static member Empty(program : Program) =
    let rec get_labels (program : Program) =
      match program with
      |[] -> []
      |Label (id, position) :: xs -> (id, position) :: get_labels xs
      |_::xs -> get_labels xs
    {
      PC = 0
      ProgramArea = program
      Memory = []
      Register = [(Reg1, Integer (0, (0,0)))
                  (Reg2, Integer (0, (0,0)))
                  (Reg3, Integer (0, (0,0)))
                  (Reg4, Integer (0, (0,0)))] |> Map.ofSeq
      Labels = program |> get_labels |> Map.ofSeq
    //  Labels  = program 
    }
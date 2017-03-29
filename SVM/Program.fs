open SVMAST

module State = 

  let add_value_to_mem (mem : Map<int, Literal>) (target : int) (value : Literal) :  Map<int, Literal> =
    match mem.TryFind(target) with
    | None -> failwith ("Found wrong location: " + string target)
    | _ -> mem.Add(target, value)
  
  let add_value_to_reg (reg : Map<Register, Literal>) (target : Register) (value : Literal) :  Map<Register, Literal> =
    match reg.TryFind(target) with
    | None -> failwith ("Found wrong location: " + string target)
    | _ -> reg.Add(target, value)

  type State = 
    {
      PC : int
      ProgramArea : Program
      Memory : Map<int, Literal>
      Register : Map<Register, Literal>
      Labels : Map<string, int>
    }

    static member Empty(program : Program) =
      let rec get_labels length (program : Program) =
        printfn "%A" program.Length
        match program with
        |[] -> []
        |Label (id, position) :: xs -> (id, length - xs.Length) :: get_labels length xs 
        |_::xs -> get_labels length xs 
      {
        PC = 0
        ProgramArea = program
        Memory = [for i in [0..100] do yield (i, Integer(0, (0, 0)))] |> Map.ofSeq 
        Register = [(Reg1, Integer (0, (0,0)))
                    (Reg2, Integer (0, (0,0)))
                    (Reg3, Integer (0, (0,0)))
                    (Reg4, Integer (0, (0,0)))] |> Map.ofSeq
        Labels = program |> get_labels program.Length |> Map.ofSeq
      //  Labels  = program 
      }
      member this.IsEOF() =
        this.PC >= this.ProgramArea.Length
      member this.Step() : State = 
        let rec get_value_of_literal (lit : Literal) (state : State) = 
          match lit with
          |Address(add) -> 
            match add with 
            |Integer(value, position) -> state.Memory.[value]
            |Register(reg, pos) ->
              match state.Register.[reg] with
              |Integer(value, pos) -> state.Memory.[value]
              |_ -> failwith ("Invalid Type Expression: Expected Integer but given " + string add) 
            |_ -> failwith ("Invalid Type Expression: Expected Integer but given " + string add)
          |Register(reg, position) -> state.Register.[reg]
          |_ -> lit

        let cur_ins = this.ProgramArea.[this.PC]              
        match cur_ins with
        | Nop(position) ->
          {this with PC = this.PC + 1}
        
        | Mov (sourceLit, valueLit, position) -> 
          match sourceLit with
          |Address(add) -> 
            match add with
            |Integer(value, pos) ->
              {this with Memory = add_value_to_mem this.Memory value (get_value_of_literal valueLit this); PC = this.PC + 1 }
            |Register(reg, pos) ->
              match this.Register.[reg] with
              |Integer(value, _) ->
                {this with Memory = add_value_to_mem this.Memory value (get_value_of_literal valueLit this); PC = this.PC + 1 }
              |_ -> failwith ("Exception")
              // |Float(value, _) ->
              //   {this with Memory = add_value_to_mem this.Memory intvalue (get_value_of_literal valueLit this); PC = this.PC + 1 }
            |_ -> failwith ("Invalid Type Expression: Expected Integer but given " + string add + " at " + string position ) 
          |Register(reg, position) ->
            {this with Register = add_value_to_reg this.Register reg (get_value_of_literal valueLit this); PC = this.PC + 1}
          |_ -> failwith ("Wrong argument Exception at: " + string position)
        
        | Label(id, pos) ->
          {this with PC = this.PC + 1}
        
        | And(reg, lit, pos) ->
          match (this.Register.[reg] ,get_value_of_literal lit this) with
          | Integer(val1, _), Integer(val2, _) ->
            match (val1, val2) with
            |x, y when x >= 0 && y >= 0 ->
              {this with Register = add_value_to_reg this.Register reg (Integer(1, (0,0))); PC = this.PC + 1}
            |_ -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(-1, (0,0))); PC = this.PC + 1}
          |_ -> failwith ("Wrong argument Exception at: " + string pos)

        | Or(reg, lit, pos) ->
          match (this.Register.[reg] ,get_value_of_literal lit this) with
          | Integer(val1, _), Integer(val2, _) ->
            match (val1, val2) with
            |x, y when x < 0 && y < 0 ->
              {this with Register = add_value_to_reg this.Register reg (Integer(-1, (0,0))); PC = this.PC + 1}
            |_ -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(1, (0,0))); PC = this.PC + 1}
          |_ -> failwith ("Wrong argument Exception at: " + string pos)

        | Not(reg, pos) ->
           match this.Register.[reg] with
           |Integer(value, _) when value >= 0 -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(-1, (0,0))); PC = this.PC + 1}
           |Integer(value, _) when value < 0 -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(0, (0,0))); PC = this.PC + 1}
           |_ -> failwith ("Wrong argument Exception at: " + string pos)

        | Mod(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) -> 
            {this with Register = add_value_to_reg this.Register reg (Integer((val1 % val2),(0,0))); PC = this.PC + 1}  
          |Float(val1, _), Float(val2, _) ->  
            {this with Register = add_value_to_reg this.Register reg (Float((val1 % val2),(0,0))); PC = this.PC + 1} 
          |_ -> failwith ("Wrong argument Exception at: " + string pos)

        | Add(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) -> 
            {this with Register = add_value_to_reg this.Register reg (Integer((val1 + val2),(0,0))); PC = this.PC + 1}  
          |Float(val1, _), Float(val2, _) ->  
            {this with Register = add_value_to_reg this.Register reg (Float((val1 + val2),(0,0))); PC = this.PC + 1} 
          |_ -> failwith ("Wrong argument Exception at: " + string pos)
        
        | Sub(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) -> 
            {this with Register = add_value_to_reg this.Register reg (Integer((val1 - val2),(0,0))); PC = this.PC + 1}  
          |Float(val1, _), Float(val2, _) ->  
            {this with Register = add_value_to_reg this.Register reg (Float((val1 - val2),(0,0))); PC = this.PC + 1} 
          |_ -> failwith ("Wrong argument Exception at: " + string pos)
        
        | Mul(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) -> 
            {this with Register = add_value_to_reg this.Register reg (Integer((val1 * val2),(0,0))); PC = this.PC + 1}  
          |Float(val1, _), Float(val2, _) ->  
            {this with Register = add_value_to_reg this.Register reg (Float((val1 * val2),(0,0))); PC = this.PC + 1} 
          |_ -> failwith ("Wrong argument Exception at: " + string pos)
        
        | Div(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) -> 
            {this with Register = add_value_to_reg this.Register reg (Integer((val1 / val2),(0,0))); PC = this.PC + 1}  
          |Float(val1, _), Float(val2, _) ->  
            {this with Register = add_value_to_reg this.Register reg (Float((val1 / val2),(0,0))); PC = this.PC + 1} 
          |_ -> failwith ("Wrong argument Exception at: " + string pos)
        
        | Cmp(reg, lit, pos) -> 
          match (this.Register.[reg], get_value_of_literal lit this) with
          |Integer(val1, _), Integer(val2, _) ->
            match (val1, val2) with 
            |x, y when x < y ->  
              {this with Register = add_value_to_reg this.Register reg (Integer(-1,(0,0))); PC = this.PC + 1}
            |x, y when x > y ->
              {this with Register = add_value_to_reg this.Register reg (Integer(1,(0,0))); PC = this.PC + 1}
            |_ -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(0,(0,0))); PC = this.PC + 1}
          |Float(val1, _), Float(val2, _) ->
            match (val1, val2) with 
            |x, y when x < y ->  
              {this with Register = add_value_to_reg this.Register reg (Integer(-1,(0,0))); PC = this.PC + 1}
            |x, y when x > y ->
              {this with Register = add_value_to_reg this.Register reg (Integer(1,(0,0))); PC = this.PC + 1}
            |_ -> 
              {this with Register = add_value_to_reg this.Register reg (Integer(0,(0,0))); PC = this.PC + 1}
          |_ -> failwith ("Wrong argument Exception at: " + string pos)

        | Jmp(id, pos) ->
          match this.Labels.TryFind(id) with
          | None -> failwith ("Label not found Exception at: " + string pos)
          | Some(line) ->
           {this with PC = line} 

        | Jc(id, reg, pos) ->
          match this.Register.[reg] with
          |Integer(value, pos) when value >= 0 ->  
            match this.Labels.TryFind(id) with
            | None -> failwith ("Label not found Exception at: " + string pos)
            | Some(line) ->
              {this with PC = line} 
          |Float(value, pos) when value >= 0.0 ->  
            match this.Labels.TryFind(id) with
            | None -> failwith ("Label not found Exception at: " + string pos)
            | Some(line) ->
              {this with PC = line} 
          |_ -> {this with PC = this.PC + 1}   
        

        | Jeq(id, reg, pos) ->
          match this.Register.[reg] with
          |Integer(value, pos) when value = 0 ->  
            match this.Labels.TryFind(id) with
            | None -> failwith ("Label not found Exception at: " + string pos)
            | Some(line) ->
              {this with PC = line} 
          |Float(value, pos) when value = 0.0 ->  
            match this.Labels.TryFind(id) with
            | None -> failwith ("Label not found Exception at: " + string pos)
            | Some(line) ->
              {this with PC = line} 
          |_ -> {this with PC = this.PC + 1}

        |_ -> failwith ("Not implemented Exception") 

        override m.ToString() =
          "{\n" + 
          "\tPC: " + (if m.IsEOF() then "EOF" else string m.PC)  + "\n" +
          "\tCurrentInstruction: " + (if m.IsEOF() then "null" else sprintf "%A" m.ProgramArea.[m.PC])  + "\n" +
          "\tMemory: \n" + (m.Memory |>
                                      Map.toSeq |>
                                      Seq.fold(fun s (k:int, v:Literal) -> s + "\t\tMemory[" + string k + "] -> " + string v) "") +
          "\tRegisters: \n" + (m.Register |>
                                      Map.toSeq |> 
                                      Seq.fold(fun s (id, v) ->
                                                    s + "\t\tregister name " + string id + ": " + string v + "\n") "") +
          "\n}"

// type Literal =
// | Integer of int * Position
// | Float of float * Position
// | String of string * Position
// | Address of Literal
// | Register of Register * Position

// type Instruction =
// | Nop of Position
// | Mov of Literal * Literal * Position
// | And of Register * Literal * Position
// | Or of Register * Literal * Position
// | Not of Register * Position
// | Mod of Register * Literal * Position
// | Add of Register * Literal * Position
// | Sub of Register * Literal * Position
// | Mul of Register * Literal * Position
// | Div of Register * Literal * Position
// | Cmp of Register * Literal * Position
// | Jmp of string * Position
// | Jc of string * Register * Position
// | Jeq of string * Register * Position
// | Label of string * Position
open System
open System.IO
open ParserUtils
open SVM
open Microsoft.FSharp.Text.Lexing
open State

let parseFile (fileName : string) =
  let inputChannel = new StreamReader(fileName)
  let lexbuf = LexBuffer<char>.FromTextReader inputChannel
  let parsedAST = Parser.start Lexer.tokenstream lexbuf
  parsedAST

let NOP = None
//let MOV = 

let rec eval (state : State) =
  if state.IsEOF() then printfn "The program is over.."
  else
    let state' = state.Step()
    // System.Console.Clear()
    printfn "%A" (string state')
    System.Console.ReadLine() |> ignore
    eval state'

[<EntryPoint>]
let main argv =
  try
    if argv.Length = 2 then
      let ast = parseFile argv.[0]
      do printfn "%A" ast
      let state = State.Empty(ast)
      eval state
      0
    else
      do printfn "You must specify a command line argument containing the path to the program source file and the size of the memory"
      1
  with
  | ParseError(msg,row,col) ->
      do printfn "Parse Error: %s at line %d column %d" msg row col
      1
  | :? Exception as e ->
      do printfn "%s" e.Message
      1

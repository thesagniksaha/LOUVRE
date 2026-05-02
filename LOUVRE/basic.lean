-- Test lean file / playground

def hello := "world"
def master : IO Unit :=
  IO.println s!"Hello, {hello}!"
#eval master

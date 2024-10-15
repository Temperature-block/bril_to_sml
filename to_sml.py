import copy
from dict_insnref import sml_correspondence
import re


def replace_invalid_names(sml_code):
    # Regular expression to match invalid names like a.1, one.2
    # This pattern matches names that consist of letters, digits, and a dot, like a.1
    pattern = re.compile(r'\b([a-zA-Z_]\w*)\.(\d+)\b')
    
    # Function to replace dots with underscores
    def replace(match):
        name, number = match.groups()
        return f'{name}_{number}'
    
    # Replace invalid names using the regex pattern
    modified_code = pattern.sub(replace, sml_code)
    return modified_code

def build_header(d):
    #print(d)
    header = []
    num_columns = len(next(iter(d.values())))
    #print(num_columns)
    for i in range(num_columns):
        bigger_string = ','.join(d[key][i] if i < len(d[key]) else '' for key in d)
        if bigger_string not in header:
            header.append(bigger_string)
    
    return header


def insert_children_before_let(nblk, childs):
    # Extract the list of strings from nblk
    strings = nblk[1:]
    #for child in childs:
        #print("inss--------------->",child)
    # Create the insertion text from the childs list
    insertion_text = '\n'.join(
    f"{'fun' if i == 0 else 'and'} {child[4:]}" for i, child in enumerate(childs)
    )
    #print("insss",insertion_text)
    # Process each string in the list
    result_strings = []
    for blk in strings:
        #print("yems",blk,strings)
        let_index = blk.find('in')
        fun_index = blk.find('fun')

        if let_index == -1:
            result_strings.append(blk)
        else:
            modified_blk = blk[:let_index] + insertion_text + '\n' + blk[let_index:]
            result_strings.append(modified_blk)
    
    # Return the result in the format [[], modified_string1, modified_string2, ...]
    return [nblk[0]] + result_strings

'''
def insert_children_before_let(nblk, childs):
    """
    Inserts the childs (code fragments) before the first occurrence of 'fun' 
    in the code blocks. If no 'fun' is found, inserts before 'let'.
    
    Parameters:
    nblk (list of str): List of code blocks, where the first element may be metadata.
    childs (list of str): Code fragments to insert.
    
    Returns:
    list of str: The modified list of code blocks.
    """
    # Extract the list of code blocks from nblk, skipping the metadata
    code_blocks = nblk[1:]
    
    # Create the insertion text from the childs list
    insertion_text = '\n'.join(childs)
    
    # Process each block in the list
    result_blocks = []
    for block in code_blocks:
        # Find the first occurrence of 'fun'
        fun_index = block.find('fun')
        
        if fun_index != -1:  # If 'fun' is found
            # Insert before the first 'fun'
            modified_block = block[:fun_index] + insertion_text + '\n' + block[fun_index:]
        else:
            # No 'fun' found, proceed to find 'let'
            let_index = block.find('let')
            if let_index != -1:
                # Insert before 'let'
                modified_block = block[:let_index] + insertion_text + '\n' + block[let_index:]
            else:
                # Neither 'fun' nor 'let' found, leave the block unchanged
                modified_block = block
        
        result_blocks.append(modified_block)
    
    return result_blocks'''

def format_blk(blk):
    #print("FOrmat blocku",blk)
    items = blk[0]
    #for item in items:
        #print("itm++++++++++++++++++",item)
    combined_strings = "\n".join(blk[1:]) + "\n"
    result = "\n".join(f"{item}{combined_strings}" for item in items)
    return result

def find_sublist(jmp_lbl, orig):
    for sublist in orig:
        if sublist and sublist[0].get("label") == jmp_lbl:
            return sublist

def sml_elaborator(orig,sml_insn,prgrm,tree,get):
    #print(sml_insn)
    childs = []
    children_to_synthesize = tree[get]
    for child in children_to_synthesize:
        childs.append(sml_elaborator(orig,sml_insn,prgrm,tree,child))

    blk = sml_insn[get]
    blk_orig = orig[get]
    #print(blk_orig)
    cblk_name = blk_orig[0]["label"]
    #print("yems",blk)
    #legalize jumps
    if "op" in blk[-1]:
       if blk[-1]["op"] == "jmp":
          jmp_lbl = blk[-1]["labels"][0]
          ins = " {call} "
          args = []
          required = find_sublist(jmp_lbl,orig)
          #print(jmp_lbl,required,orig)
          collected_phi = [ins for ins in required if "op" in ins and ins["op"] == "phi"]
          for phi in collected_phi:
              if "__undefined" in phi["args"]: optional = True
              else : optional = False
              lbls = phi["labels"]
              indx = lbls.index(cblk_name)
              if optional:
                 if phi["args"][indx] == "__undefined":
                    args.append("NONE")
                 else:
                    args.append("SOME("+phi["args"][indx]+")")
              else:
                 args.append(phi["args"][indx])
          #print(args)
          if args != []:
              #print(args)
              args = ",".join(args)
          else:
              args = "()"
          if args == "()":
             blk[-1] =  "in "+ jmp_lbl+" ("+ ")"+" end"
          else:
             blk[-1] =  "in "+ jmp_lbl+" (" +args +")"+" end"
          #print("yems2",blk,args,blk[-1])
          #blk[-1] =  "in "+ jmp_lbl+" (" +args +")"+" end"
       elif blk[-1]["op"] == "br":
          jmp_lbl = blk[-1]["labels"]
          calls = []
          for i in jmp_lbl:
              args = []
              required = find_sublist(i,orig)
              collected_phi = [ins for ins in required if "op" in ins and ins["op"] == "phi"]
              for phi in collected_phi:
                  if "__undefined" in phi["args"]: optional = True
                  else : optional = False
                  lbls = phi["labels"]
                  indx = lbls.index(cblk_name)
                  if optional:
                     if phi["args"][indx] == "__undefined":
                        args.append("NONE")
                     else:
                        args.append("SOME("+phi["args"][indx]+")")
                  else:
                     args.append(phi["args"][indx])
              if args != []:
                 args = ",".join(args)
              else:
                 args = "()"

              if args == "()":
                 call = i + args
              else:
                 call = i+" ("+args+")"
              calls.append(call)
          blk[-1] = "in "+"if "+blk[-1]["args"][0]+" then "+calls[0]+" else "+calls[1] +" end"

    #nblk = format_blk(blk)
    nblk = insert_children_before_let(blk, childs)
    nblk = format_blk(nblk)
    #print(nblk)
    return nblk

def legalize_blocks_entry(blk):
    #print(blk)
    has_parametric = False
    collected_phi = [ins for ins in blk if "op" in ins and ins["op"] == "phi"]
    farg_mapping = {}
    fn = ""

    for phi in collected_phi:
        if "__undefined" in phi["args"]: optional = True
        else : optional = False
        for lbl_no,lbl in enumerate(phi["labels"]):
            if phi["dest"] not in farg_mapping:
              if optional:
                 if phi["args"][lbl_no] != "__undefined":
                    farg_mapping[phi["dest"]]  = ["SOME("+phi["dest"]+")"]
                 else:
                    farg_mapping[phi["dest"]]  = ["NONE"]
              else:
                    farg_mapping[phi["dest"]]  = [phi["dest"]]

            else:
              if optional:
                 if phi["args"][lbl_no] != "__undefined":
                    farg_mapping[phi["dest"]].append("SOME("+phi["dest"]+")")
                 else:
                    farg_mapping[phi["dest"]].append("NONE")
              else:
                    farg_mapping[phi["dest"]]  = [phi["dest"]]
    

    if collected_phi != []:
       entry = blk[0]
       if "label" in entry:
          fn = fn + "fun " + entry["label"]
          altfn = "| " + entry["label"]
       fn = fn+"({args})"
       altfn = altfn+"({args})"
       header_args = build_header(farg_mapping)
       header = []
       for i_num,i in enumerate(header_args):
           if i_num == 0:
              header.append(fn.format(args = i) +" = let ")
           else:
              header.append(altfn.format(args = i) +" = let ")
    else:
       entry = blk[0]
       if "label" in entry:
          fn = fn + "fun " + entry["label"] +"() = let "
       header = [fn]

    blk = [ins for ins in blk if not ("op" in ins and ins["op"] == "phi")]
    blk = [ins for ins in blk if not ("label" in ins)]
    blk.insert(0, header)
    return blk

def legalize_returns(blk):
    #print(blk)
    last_inst = blk[-1]
    if "op" in last_inst and last_inst["op"] == "ret":
       if "args" in last_inst:
          blk[-1] = "in {}".format(last_inst["args"][0])
       else:
          blk[-1] = "in ()"
    return blk


def infer_type(var,alblks):
    #print(var)
    arith = {
    "add": "+",
    "sub": "-",
    "mul": "*",
    "div": "/"
    }

    blop = {
    "eq": "=",   # Equal (Python)
    "lt": "<",    # Less than
    "gt": ">",    # Greater than
    "le": "<=",   # Less than or equal to
    "ge": ">=",   # Greater than or equal to
    "and": "andalso",  # Logical AND (SML)
    "or": "orelse"     # Logical OR (SML)
    }

    for blk in alblks:
        for instr in blk:
            if "dest" in instr:
               if instr["dest"] == var:
                  if instr["op"] == "id":
                     return infer_type(instr["args"][0],alblks)
                  elif instr["op"] == "phi":
                       return infer_type(instr["args"][0],alblks)
                  else:
                     if "type" in instr:
                        #print("yems",instr["type"])
                        if instr["type"] == "bool":
                           return "BoolType"
                        else:
                           return "IntType"

def synthesize_block_instrs(blk,alls):
    al = alls
    #print(blk)
    mlins = copy.deepcopy(sml_correspondence)
    #print(blk)
    arith = {
    "add": "+",
    "sub": "-",
    "mul": "*",
    "div": "/"
    }

    blop = {
    "eq": "=",   # Equal (Python)
    "lt": "<",    # Less than
    "gt": ">",    # Greater than
    "le": "<=",   # Less than or equal to
    "ge": ">=",   # Greater than or equal to
    "and": "andalso",  # Logical AND (SML)
    "or": "orelse"     # Logical OR (SML)
    }

    new_insns = []
    instr_ = None
    for instr_num,instr in enumerate(blk):
        if("op" in instr):
            if(instr["op"] in arith):
               #"arith_op":"val {dest} :int = {arg1} {op} {arg2};"
               instr_ = copy.deepcopy(mlins["arith_op"])
               instr_ = instr_.format(dest=instr["dest"],arg1=instr["args"][0],arg2=instr["args"][1],op=arith[instr["op"]])
            elif(instr["op"] in blop):
               instr_ = copy.deepcopy(mlins["arith_op"])
               instr_ = instr_.format(dest=instr["dest"],arg1=instr["args"][0],arg2=instr["args"][1],op=blop[instr["op"]])
            elif(instr["op"] == "not"):
                 #"not": "val {dest} :bool = not {arg1};", 
                 #{'args': ['x'], 'dest': 'xn', 'op': 'not', 'type': 'bool'} ,
                 instr_ = copy.deepcopy(mlins["not"])
                 instr_ = instr_.format(dest=instr["dest"],arg1=instr["args"][0])
            #const
            elif(instr["op"] == "const"):
               instr_ = copy.deepcopy(mlins["const"])
               if(isinstance(instr["value"], bool) and instr["value"] == True):
                  val = "true"
               elif(isinstance(instr["value"], bool) and instr["value"] == False):
                  val = "false"
               else:
                  val = instr["value"]
               instr_ = instr_.format(dest=instr["dest"],arg1=val)
               #print("constss",instr["value"],val,instr_)

            elif(instr["op"] == "id"):
               instr_ = copy.deepcopy(mlins["id"])
               instr_ = instr_.format(dest=instr["dest"],arg1=instr["args"][0])

            elif(instr["op"] == "nop"):
               continue

            elif(instr["op"] == "ret"):
               instr_ = instr

            elif(instr["op"] == "call"):
               name = instr["funcs"][0]
               if("args" in instr):
                   for arg in instr["args"]:
                       name = name +" "+arg
               if("dest" in instr):
                  name = "val " + instr["dest"] + name
               instr_=name

            elif(instr["op"] == "print"):
                 convargs = []
                 for arg in instr["args"]:
                     typ = infer_type(arg,al)
                     #print("yems",arg,typ)
                     convargs.append("("+typ+"("+arg+"))")
                 convargs = ",".join(convargs)
                 if(instr_num == len(blk)-1):
                    instr_ = "in accumulate_and_prnt ["+convargs+"] end"
                 else:
                    instr_ = "val _  = accumulate_and_prnt ["+convargs+"]"

            elif(instr["op"] == "jmp" or instr["op"] == "br" or instr["op"] == "phi"):
               instr_ = instr

            new_insns.append(instr_)

        else:
            new_insns.append(instr)

    return new_insns

def to_sml(ext,prgrm,tree):
    prnt = '''
datatype anyType = IntType of int | BoolType of bool

fun to_str (IntType x) = Int.toString x
  | to_str (BoolType b) = Bool.toString b

fun printoverloaded [] track = print track
  | printoverloaded (x::xs) track =
      let
        val str = track ^ (to_str x) ^ "\\n"
      in
        printoverloaded xs str
      end;

fun accumulate_and_prnt list =
  let
    val initialTrack = ""
    (* Call the recursive printoverloaded function *)
    val _ = printoverloaded list initialTrack
  in
    ()
  end;

'''
    #print(ext)
    #print("--------------------------------")
    #print(prgrm)
    sml_insn = []
    #print("--idom--------->",prgrm[1][1]['meta']['idom'])
    phldr = []
    orig = []
    for key, value in sorted(prgrm.items()):
      orig.append(value[0])

    for key, value in sorted(prgrm.items()):
      sml_insn.append(synthesize_block_instrs(value[0],orig))
      #orig.append(value[0])

    for blk_num,blk in enumerate(sml_insn):
        sml_insn[blk_num] = legalize_blocks_entry(legalize_returns(blk))
        #print("---++---",sml_insn[blk_num])

    elab = sml_elaborator(orig,sml_insn,prgrm,tree,0)
    #print("------------------>")
    #print(elab)
    #print("------------------>")
    #print(ext["name"])
    total = "fun "+ext["name"]+"("
    if "args" in ext:
       for i in ext["args"]:
           total += i["name"]+","
    total = total + ")"
    total  = total.replace(",)",")")
    total = total + " = let "+prnt +" \n "+elab  + "in "+orig[0][0]["label"]+"()"+" end"
    print(replace_invalid_names(total))

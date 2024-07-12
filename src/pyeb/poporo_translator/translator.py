import sys, re
from antlr4 import *
from .Python3Parser import Python3Parser
from .Python3ParserVisitor import Python3ParserVisitor
from antlr4.tree.Tree import TerminalNodeImpl

from z3 import *

class translator(Python3ParserVisitor):

    def myprint(self,s):
        b = False
        if b:
            print(s)
    
    # Visit a parse tree produced by Python3Parser#single_input.
    def visitSingle_input(self, ctx:Python3Parser.Single_inputContext):
        self.myprint('visitSingle_input')
        res = self.visitChildren(ctx)
        return res
    
    
    # Visit a parse tree produced by Python3Parser#file_input.
    def visitFile_input(self, ctx:Python3Parser.File_inputContext):
        self.myprint('visitFile_input')
        res = ""
        obj_dict = {} # dictionary of class x object created 
        for i in range(0,ctx.getChildCount()):
            if not isinstance(ctx.getChild(i),TerminalNodeImpl):
                r, d = self.visit(ctx.getChild(i))
                
                # positive lookbehind - 
                # it returns self.context's class-name
                context = re.search(r"\b(?<=self.context:)(\w)+", r)
                if context != None:
                    context_class = context.group() # self.context's class-name
                    context_class_obj = obj_dict[context_class] # self.context's object
                    # self.context.f becomes obj_f
                    r = re.sub(r"\b%s\b"%'self\.context\.',context_class_obj+"_",r)
                    # it removes 'self.context:'
                    r = re.sub(r"self.context:", "", r)
                    # self.context becomes obj
                    r = re.sub(r"\b%s\b"%'self\.context',context_class_obj,r)
                res += r
                obj_dict.update(d)

        res = re.sub(r"^\s+", "", res, flags=re.UNICODE) # it removes leading spaces
        res = re.sub(r"\s+$", "", res, flags=re.UNICODE) # it removes trailing spaces

        # ClassName are replaced with Obj
        for class_name in obj_dict.keys():            
            # final handling of 'super().event_aaa()'
            res = re.sub(r"\b%s\.\b"%class_name,obj_dict[class_name]+"_",res)
            #
            res = re.sub(r"\b%s\b"%class_name,obj_dict[class_name],res)

        # final handling of super().__init__(aaa.bbb)  
        # here we match '(sub_class,super_class).__init__'
        # goal: every field of the super_class becomes a field in the sub_class
        pattern1 = r'\((.*?):(.*?)\).__init__' # (sub_class,super_class) tuples
        lst1 = re.findall(pattern1,res) # finall handles many sub-classes of a particular class
        
        super_init_str = ""
        for pair in lst1: # for earch (class_obj,super_class_obj) pair
            #print('pair ', str(pair))
            temp_str = "\n"
            sub_class = pair[0] # class object
            super_class = pair[1] # super-class object
            #
            pattern2 = r'%s_(\w+)='%super_class # list of all the super_class object elements
            lst_all_elms = re.findall(pattern2,res) #
            #print('lst_all_elms ', str(lst_all_elms))
            # removing elements: event_*, ref_event_*, invariant_*, axioms_*, and theorem_*
            lst_obj_fields = [ elm for elm in lst_all_elms
                                   if not(elm.startswith('event_') or \
                                              elm.startswith('invariant_') or \
                                              elm.startswith('theorem_') or \
                                              elm.startswith('axiom_') or \
                                              elm.startswith('ref_event_'))
                                   ]
            lst_obj_fields = list( dict.fromkeys(lst_obj_fields) )  # it removes duplicates  
            #
            for field in lst_obj_fields:
                    # sub_class_field = super_class_field for each pair
                    temp_str += (sub_class+"_"+field+"="+super_class+"_"+field+"\n")
            super_init_str += temp_str
            super_init_str = re.sub(r"^\s+", "", super_init_str, flags=re.UNICODE) # removing leading spaces
            super_init_str = re.sub(r"\s+$", "", super_init_str, flags=re.UNICODE) # removing trailing spaces 
            pattern3 = "\("+sub_class+":"+super_class+"\)."+"__init__"
            assert super_init_str # checking non-emptyness : 
            # we substitute (super_class_obj:class_obj).__init__ with super_init_str
            res = re.sub(pattern3,super_init_str,res)

        # the proofs obligations are generated for the last machine refinement    
        keys = list(obj_dict.keys())
        str_machine = '\n__machine__ = '+obj_dict[keys[-1]]
        res += str_machine
        
        return res, obj_dict
    

    # Visit a parse tree produced by Python3Parser#eval_input.
    def visitEval_input(self, ctx:Python3Parser.Eval_inputContext):
        self.myprint('visitEval_input')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#decorator.
    def visitDecorator(self, ctx:Python3Parser.DecoratorContext):
        self.myprint('visitDecorator')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#decorators.
    def visitDecorators(self, ctx:Python3Parser.DecoratorsContext):
        self.myprint('visitDecorators')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#decorated.
    def visitDecorated(self, ctx:Python3Parser.DecoratedContext):
        self.myprint('visitDecorated')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#async_funcdef.
    def visitAsync_funcdef(self, ctx:Python3Parser.Async_funcdefContext):
        self.myprint('visitAsync_funcdef')        
        return self.visitChildren(ctx)
    
    
    # Visit a parse tree produced by Python3Parser#funcdef.
    def visitFuncdef(self, ctx:Python3Parser.FuncdefContext):
        self.myprint('visitFuncdef ')
        par_lst = self.visitParameters(ctx.parameters()) # list of parameters
        func_name = self.visitName(ctx.name()) # fucntion name
        block = self.visitBlock(ctx.block()) # block of instructions

        res = ""
        if func_name.startswith("event_"):
            evt_name = func_name
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removing leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removing trailing spaces
            
            block_lst = block.split('\n')            
            return_stm = block_lst[-1] # last instruction: the return statement
            block_lst = block_lst[:-1] # it removes the last instruction
            for expr_stmt in block_lst:
                lr = expr_stmt.split('=')    
                if len(lr) > 1: # if expr_stmt is an assignment statement            
                    lefthand = lr[0] # lefthand part of the assignment
                    pattern = r'(?<!\')(\b%s\b)'%lefthand # we replace lefthand as long it's not preceded by \'
                    replacement = r'self.%s_%s'%(evt_name,lefthand)
                    block = re.sub(pattern,replacement,block)                        
                    # abc block = re.sub(r"\b%s\b"%lefthand,"self."+evt_name+"_"+lefthand,block) # replaces lefthand everywhere in the block
            block = block.replace("return ","self."+evt_name+"=")
            res = block+"\n"
            
            if evt_name == 'event_initialisation':
                res += 'selF.add_initevt(self.'+evt_name+')'
            else:    
                # abc res += 'selF.add_event(\'self.'+evt_name+'\',self.'+evt_name+')'
                res += 'selF.add_event(self.'+evt_name+')'
        elif func_name.startswith("ref_event_"):
            evt_name = func_name
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # it removes leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # it removes trailing spaces            
            block_lst = block.split('\n')            
            return_stm = block_lst[-1] # 'return' is the last instruction
            block_lst = block_lst[:-1] # it removes the last instruction
            for expr_stmt in block_lst:
                lr = expr_stmt.split('=') # left-right expression statement
                if len(lr) > 1: # if expr_stmt is an assignment statement
                    lefthand = lr[0] # lefthand part of the assignment
                    pattern = r'(?<!\')(\b%s\b)'%lefthand # we replace lefthand as long it's not preceded by \'
                    replacement = r'self.%s_%s'%(evt_name,lefthand)
                    block = re.sub(pattern,replacement,block)                        
                    # abc block = re.sub(r"\b%s\b"%lefthand,"self."+evt_name+"_"+lefthand,block) # replaces lefthand everywhere
            block = block.replace("return ","self."+evt_name+"=")
            res = block+"\n"
            if evt_name == 'ref_event_initialisation':
                res += 'selF.add_ref_initevt(self.'+evt_name+')'
            else:    
                res += 'selF.add_ref_event(self.'+evt_name+')'
        elif func_name.startswith("invariant_"):    
            inv_name = func_name
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # it removes leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # it removes trailing spaces
            
            block_lst = block.split('\n')
            return_stm = block_lst[-1] # the last instruction is the return statement
            block_lst = block_lst[:-1] # remove the last instruction
            for expr_stmt in block_lst:
                lr = expr_stmt.split('=') 
                if len(lr) > 1: # if expr_stmt is an assignment statement
                    lefthand = lr[0] # lefthand part of the assignment
                    pattern = r'(?<!\')(\b%s\b)'%lefthand # we replace lefthand as long it's not preceded by \'
                    replacement = r'self.%s_%s'%(inv_name,lefthand)
                    block = re.sub(pattern,replacement,block)                        
                    #abc block = re.sub(r"\b%s\b"%lefthand,"self."+inv_name+"_"+lefthand,block) # replace lefthand  everywhere
            block = block.replace("return ","self."+inv_name+"=")
            res = block+"\n"
            res += 'selF.add_invariant(\'self.'+inv_name+'\',self.'+inv_name+')'  
        elif func_name.startswith("axiom_"):
            axm_name = func_name
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removing leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removing trailing spaces
            
            block_lst = block.split('\n')
            return_stm = block_lst[-1] # 'return' is the last instruction
            block_lst = block_lst[:-1] # it removes the last instruction
            for expr_stmt in block_lst:
                lr = expr_stmt.split('=') 
                if len(lr) > 1: # if expr_stmt is an assignment statement
                    lefthand = lr[0] # lefthand part of the assignment
                    pattern = r'(?<!\')(\b%s\b)'%lefthand # we replace lefthand as long it's not preceded by \'
                    replacement = r'self.%s_%s'%(axm_name,lefthand)
                    block = re.sub(pattern,replacement,block)                        
                    #abc block = re.sub(r"\b%s\b"%lefthand,"self."+axm_name+"_"+lefthand,block) # replaces lefthand everywhere
            block = block.replace("return ","self."+axm_name+"=")
            res = block+"\n"
            res += 'selF.add_axiom(\'self.'+axm_name+'\',self.'+axm_name+')'
        elif func_name.startswith("theorem_"):
            thm_name = func_name
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removes leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removes trailing spaces
            
            block_lst = block.split('\n')
            return_stm = block_lst[-1] # 'return' is the last instruction
            block_lst = block_lst[:-1] # it removes the last instruction
            for expr_stmt in block_lst:
                lr = expr_stmt.split('=') 
                if len(lr) > 1: # if expr_stmt is an assignment statement
                    lefthand = lr[0] # lefthand part of the assignment
                    pattern = r'(?<!\')(\b%s\b)'%lefthand # we replace lefthand as long it's not preceded by \'
                    replacement = r'self.%s_%s'%(thm_name,lefthand)
                    block = re.sub(pattern,replacement,block)                        
                    #abc block = re.sub(r"\b%s\b"%lefthand,"self."+thm_name+"_"+lefthand,block) # replaces lefthand everywhere
            block = block.replace("return ","self."+thm_name+"=")
            res = block+"\n"
            res += 'selF.add_theorem(\'self.'+thm_name+'\',self.'+thm_name+')'
        elif func_name.startswith("__init__"):
            if len(par_lst) == 1: # __init__ within Context
                block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removing leading spaces
                block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removing trailing spaces
                block_lst = block.split('\n')
                for expr_stmt in  block_lst:
                    lr = expr_stmt.split('=')
                    lefthand = lr[0] # lefthand part of the assignment
                    righthand = lr[1] # righthand part of the assignment
                    leftvar = lefthand.replace('self.','')
                    # it replaces self.x = Int('x') with self.x = Int('self.x')
                    righthand = re.sub(r"\b%s\b"%leftvar,lefthand,righthand) 
                    res += (lefthand+"="+righthand+"\n")
                    res += 'selF.add_constant(\''+lefthand+'\','+lefthand+')\n'
                # res += block
                res = re.sub(r"\n$", "", res, flags=re.UNICODE) # removing the last '\n'

            elif len(par_lst) == 2: # Abstract Machine, __init__
                index = par_lst[1].find(':') # context object : context object type
                context_par = par_lst[1][:index] # parameter contex and 
                context_par_type = par_lst[1][index+1:] # its type

                self_str = 'self=BMachine('+context_par_type+')\n'
                res = self_str + res                        

                block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removes leading spaces
                block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removes trailing spaces
                block_lst = block.split('\n')
                
                left_block_lst = [expr_stmt.split('=')[0] for expr_stmt in block_lst]
                assert 'self.context' in left_block_lst   # 'self.context' should appear as a lefhand part
                
                for expr_stmt in  block_lst:
                    lr = expr_stmt.split('=')
                    lefthand = lr[0] # lefthand part of the assignment
                    righthand = lr[1] # righthand part of the assignment
                    
                    if re.search(context_par,righthand):
                        # negative lookbehind -
                        # it replaces every occurrence of context_par that's
                        # not preceded by 'self.' with context_par:context_par_type
                        righthand = re.sub(r"\b(?<!self.)%s\b"%context_par,context_par+":"+context_par_type,righthand)
                    leftvar = lefthand.replace('self.',"")
                    # it replaces "self.r = Int('r')" with "self.r = Int('self.r')"
                    # it replaces x by self.x in righthand
                    righthand = re.sub(r"\b%s\b"%leftvar,"self."+leftvar,righthand)
                    res += (lefthand+"="+righthand+"\n")
                    if lefthand == 'self.context': # BMachine , __init__
                        res += 'selF.add_context('+lefthand+')\n'
                    elif lefthand == 'self.variant':
                        res += 'selF.add_variant('+righthand+')\n'
                    else:
                        res += 'selF.add_variable('+lefthand+')\n'
                        
                res = re.sub(r"\n$", "", res, flags=re.UNICODE) # it removes the last '\n'
            elif len(par_lst) == 3: # Refinement Machine, __init__
                index = par_lst[2].find(':') # context object : context object type
                context_par = par_lst[2][:index] # parameter contex and 
                context_par_type = par_lst[2][index+1:] # its type
                
                index = par_lst[1].find(':') # abstract_machine object : abstract_machine object type
                abs_mac_par = par_lst[1][:index] # parameter contex and 
                abs_mac_par_type = par_lst[1][index+1:] # its type
                
                self_str = 'self=BMachineRefines('+abs_mac_par_type+','+context_par_type+')\n'
                res = self_str + res
                
                block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removing leading spaces
                block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removing trailing spaces
                block_lst = block.split('\n')

                super_init = block_lst[0] # the first instruction is super().__init__(abstract_machine.context)
                res += super_init+'\n'
                block_lst = block_lst[1:] # the rest of instructions
                
                left_block_lst = [expr_stmt.split('=')[0] for expr_stmt in block_lst]
                assert 'self.context' in left_block_lst   # 'self.context' must be given an initial value
                assert 'self.abstract_machine' in left_block_lst # 'self.abstract_machine' must be given a value

                for expr_stmt in  block_lst:
                    lr = expr_stmt.split('=')
                    lefthand = lr[0] # lefthand part of the assignment
                    righthand = lr[1] # righthand part of the assignment
                    
                    if re.search(context_par,righthand):
                        # negative lookbehind -
                        # it replaces every occurrence of context_par that's
                        # not preceded by 'self.' with context_par:context_par_type
                        righthand = re.sub(r"\b(?<!self.)%s\b"%context_par,context_par+":"+context_par_type,righthand) 
                    #
                    if re.search(abs_mac_par,righthand):
                        # negative lookbehind -
                        # it replaces every occurrence of abs_mac_par that's
                        # not preceded by 'self.' with abs_mac_par:abs_mac_type
                        righthand = re.sub(r"\b(?<!self.)%s\b"%abs_mac_par,abs_mac_par_type,righthand) 
                        
                    leftvar = lefthand.replace('self.',"")
                    # it replaces "self.r = Int('r')" with "self.r = Int('self.r')"
                    # it replaces x by self.x in righthand
                    righthand = re.sub(r"\b%s\b"%leftvar,"self."+leftvar,righthand)  
                    res += (lefthand+"="+righthand+"\n")
                    if lefthand == 'self.context': # BMachine , __init__
                        res += 'selF.add_context('+lefthand+')\n'
                    elif lefthand == 'self.variant':
                        res += 'selF.add_variant('+righthand+')\n'
                    else:
                        res += 'selF.add_variable('+lefthand+')\n' 
                res = re.sub(r"\n$", "", res, flags=re.UNICODE) # it removes the last '\n'             
        return res

    
    # Visit a parse tree produced by Python3Parser#parameters.
    def visitParameters(self, ctx:Python3Parser.ParametersContext):
        self.myprint('visitParameters')
        res = self.visitTypedargslist(ctx.typedargslist()) # it returns a list of strings
        return res


    # Visit a parse tree produced by Python3Parser#typedargslist.
    def visitTypedargslist(self, ctx:Python3Parser.TypedargslistContext):
        self.myprint('visitTypedargslist')        
        res = [p.strip() for p in ctx.getText().split(',')] # it returns a list of strings
        return res    
 

    # Visit a parse tree produced by Python3Parser#tfpdef.
    def visitTfpdef(self, ctx:Python3Parser.TfpdefContext):
        self.myprint('visitTfpdef')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#varargslist.
    def visitVarargslist(self, ctx:Python3Parser.VarargslistContext):
        self.myprint('visitVarargslist')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#vfpdef.
    def visitVfpdef(self, ctx:Python3Parser.VfpdefContext):
        self.myprint('visitVfpdef')
        res = self.visitChildren(ctx)
        return res

    # Visit a parse tree produced by Python3Parser#stmt.
    def visitStmt(self, ctx:Python3Parser.StmtContext):
        self.myprint('visitStmt')
        res = ""
        obj_dict = {} # dictionary of class x object created
        child = ctx.getChild(0)
        if isinstance(child,Python3Parser.Compound_stmtContext):
            res, obj_dict = self.visitCompound_stmt(child)
        else:     
            res = self.visit(child)
        return res, obj_dict
    
    
    # Visit a parse tree produced by Python3Parser#simple_stmts.
    def visitSimple_stmts(self, ctx:Python3Parser.Simple_stmtsContext):
        self.myprint('visitSimple_stmts')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res+"\n"
            else:
                res = res +self.visit(ctx.getChild(i))
                res = re.sub(r"^\s+", "", res, flags=re.UNICODE) # removing leading spaces
        return res 

    # Visit a parse tree produced by Python3Parser#simple_stmt.
    def visitSimple_stmt(self, ctx:Python3Parser.Simple_stmtContext):
        self.myprint('visitSimple_stmt')
        res = self.visitChildren(ctx)
        res = re.sub(r"^\s+", "", res, flags=re.UNICODE) # removing leading spaces
        res = re.sub(r"\s+$", "", res, flags=re.UNICODE) # removing trailing spaces
        return res
    

    # Visit a parse tree produced by Python3Parser#expr_stmt.
    def visitExpr_stmt(self, ctx:Python3Parser.Expr_stmtContext):
        self.myprint('visitExpr_stmt')
        
        res = ""
        if  ctx.getChildCount() == 3: 
            lefthand = self.visitTestlist_star_expr(ctx.testlist_star_expr(0))
            righthand = self.visitTestlist_star_expr(ctx.testlist_star_expr(1))
            res =  lefthand+'='+righthand
        elif  ctx.getChildCount() == 1: 
            res = ctx.getText()
        return res
    

    # Visit a parse tree produced by Python3Parser#annassign.
    def visitAnnassign(self, ctx:Python3Parser.AnnassignContext):
        self.myprint('visitAnnassign')
        return self.visitChildren(ctx)
    

    # Visit a parse tree produced by Python3Parser#testlist_star_expr.
    def visitTestlist_star_expr(self, ctx:Python3Parser.Testlist_star_exprContext):
        self.myprint('visitTestlist_star_expr')
        res = ctx.getText()
        return res


    # Visit a parse tree produced by Python3Parser#augassign.
    def visitAugassign(self, ctx:Python3Parser.AugassignContext):
        self.myprint('visitAugassign')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#del_stmt.
    def visitDel_stmt(self, ctx:Python3Parser.Del_stmtContext):
        self.myprint('visitDel_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#pass_stmt.
    def visitPass_stmt(self, ctx:Python3Parser.Pass_stmtContext):
        self.myprint('visitPass_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#flow_stmt.
    def visitFlow_stmt(self, ctx:Python3Parser.Flow_stmtContext):
        self.myprint('visitFlow_stmt')
        res = self.visitChildren(ctx)
        return res


    # Visit a parse tree produced by Python3Parser#break_stmt.
    def visitBreak_stmt(self, ctx:Python3Parser.Break_stmtContext):
        self.myprint('visitBreak_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#continue_stmt.
    def visitContinue_stmt(self, ctx:Python3Parser.Continue_stmtContext):
        self.myprint('visitContinue_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#return_stmt.
    def visitReturn_stmt(self, ctx:Python3Parser.Return_stmtContext):
        self.myprint('visitReturn_stmt')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res += "return " 
            else:
                res = res +self.visit(ctx.getChild(i))
        return res
    
    
    # Visit a parse tree produced by Python3Parser#yield_stmt.
    def visitYield_stmt(self, ctx:Python3Parser.Yield_stmtContext):
        self.myprint('visitYield_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#raise_stmt.
    def visitRaise_stmt(self, ctx:Python3Parser.Raise_stmtContext):
        self.myprint('visitRaise_stmt')

    # Visit a parse tree produced by Python3Parser#import_stmt.
    def visitImport_stmt(self, ctx:Python3Parser.Import_stmtContext):
        self.myprint('visitImport_stmt')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +ctx.getChild(i).getText()
            else:
                res = res +self.visit(ctx.getChild(i))
        return res
        

    # Visit a parse tree produced by Python3Parser#import_name.
    def visitImport_name(self, ctx:Python3Parser.Import_nameContext):
        self.myprint('visitImport_name')
        return ctx.getText()
    

    # Visit a parse tree produced by Python3Parser#import_from.
    def visitImport_from(self, ctx:Python3Parser.Import_fromContext):
        self.myprint('visitImport_from') 
        res = "from "
        for i in range(1,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +' ' +ctx.getChild(i).getText()
            else:
                res = res +self.visit(ctx.getChild(i))
        return res
    

    # Visit a parse tree produced by Python3Parser#import_as_name.
    def visitImport_as_name(self, ctx:Python3Parser.Import_as_nameContext):
        self.myprint('visitImport_as_name')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +" " +ctx.getChild(i).getText()
            else:
                res = res +" " +self.visit(ctx.getChild(i))
        return res


    # Visit a parse tree produced by Python3Parser#dotted_as_name.
    def visitDotted_as_name(self, ctx:Python3Parser.Dotted_as_nameContext):
        self.myprint('visitDotted_as_name')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#import_as_names.
    def visitImport_as_names(self, ctx:Python3Parser.Import_as_namesContext):
        self.myprint('visitImport_as_names')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +" " +ctx.getChild(i).getText()
            else:
                res = res +" " +self.visit(ctx.getChild(i))
        return res


    # Visit a parse tree produced by Python3Parser#dotted_as_names.
    def visitDotted_as_names(self, ctx:Python3Parser.Dotted_as_namesContext):
        self.myprint('visitDotted_as_names')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +" " +ctx.getChild(i).getText()
            else:
                res = res +" " +self.visit(ctx.getChild(i))
        return res
    

    # Visit a parse tree produced by Python3Parser#dotted_name.
    def visitDotted_name(self, ctx:Python3Parser.Dotted_nameContext):
        self.myprint('visitDotted_name')
        res = ""
        for i in range(0,ctx.getChildCount()):
            if isinstance(ctx.getChild(i),TerminalNodeImpl):
                res = res +" " +ctx.getChild(i).getText()
            else:
                res = res +" " +self.visit(ctx.getChild(i))
        res = re.sub(r"\s+", "", res, flags=re.UNICODE) # removing white spaces     
        return res


    # Visit a parse tree produced by Python3Parser#global_stmt.
    def visitGlobal_stmt(self, ctx:Python3Parser.Global_stmtContext):
        self.myprint('visitGlobal_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#nonlocal_stmt.
    def visitNonlocal_stmt(self, ctx:Python3Parser.Nonlocal_stmtContext):
        self.myprint('visitNonlocal_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#assert_stmt.
    def visitAssert_stmt(self, ctx:Python3Parser.Assert_stmtContext):
        self.myprint('visitAssert_stmt')
        return self.visitChildren(ctx)

    # Visit a parse tree produced by Python3Parser#compound_stmt.
    def visitCompound_stmt(self, ctx:Python3Parser.Compound_stmtContext):
        self.myprint('visitCompound_stmt ')
        res = ""
        obj_dict = {}  # dictionary of class x object created
        if ctx.getChildCount() > 0:
            child = ctx.getChild(0)
            if isinstance(child,Python3Parser.ClassdefContext):
                res, obj_dict = self.visitClassdef(child)
            elif isinstance(child,Python3Parser.FuncdefContext):
                res = self.visitFuncdef(child)
                
        res += "\n"
        return res, obj_dict

    # Visit a parse tree produced by Python3Parser#async_stmt.
    def visitAsync_stmt(self, ctx:Python3Parser.Async_stmtContext):
        self.myprint('visitAsync_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#if_stmt.
    def visitIf_stmt(self, ctx:Python3Parser.If_stmtContext):
        self.myprint('visitIf_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#while_stmt.
    def visitWhile_stmt(self, ctx:Python3Parser.While_stmtContext):
        self.myprint('visitWhile_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#for_stmt.
    def visitFor_stmt(self, ctx:Python3Parser.For_stmtContext):
        self.myprint('visitFor_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#try_stmt.
    def visitTry_stmt(self, ctx:Python3Parser.Try_stmtContext):
        self.myprint('visitTry_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#with_stmt.
    def visitWith_stmt(self, ctx:Python3Parser.With_stmtContext):
        self.myprint('visitWith_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#with_item.
    def visitWith_item(self, ctx:Python3Parser.With_itemContext):
        self.myprint('visitWith_item')
        return self.visitChildren(ctx)
 

    # Visit a parse tree produced by Python3Parser#except_clause.
    def visitExcept_clause(self, ctx:Python3Parser.Except_clauseContext):
        self.myprint('visitExcept_clause')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#block.
    def visitBlock(self, ctx:Python3Parser.BlockContext):
        self.myprint('visitBlock ')
        res = ""
        obj_dict = {} # dictionary of class x object created 
        for i in range(0,ctx.getChildCount()):
            context_class = ''
            if not isinstance(ctx.getChild(i),TerminalNodeImpl):
                r, d = self.visit(ctx.getChild(i))                
                res += r
                obj_dict.update(d)
        return res
    

    # Visit a parse tree produced by Python3Parser#match_stmt.
    def visitMatch_stmt(self, ctx:Python3Parser.Match_stmtContext):
        self.myprint('visitMatch_stmt')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#subject_expr.
    def visitSubject_expr(self, ctx:Python3Parser.Subject_exprContext):
        self.myprint('visitSubject_expr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#star_named_expressions.
    def visitStar_named_expressions(self, ctx:Python3Parser.Star_named_expressionsContext):
        self.myprint('visitStar_named_expressions')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#star_named_expression.
    def visitStar_named_expression(self, ctx:Python3Parser.Star_named_expressionContext):
        self.myprint('visitStar_named_expression')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#case_block.
    def visitCase_block(self, ctx:Python3Parser.Case_blockContext):
        self.myprint('visitCase_block')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#guard.
    def visitGuard(self, ctx:Python3Parser.GuardContext):
        self.myprint('visitGuard')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#patterns.
    def visitPatterns(self, ctx:Python3Parser.PatternsContext):
        self.myprint('visitPatterns')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#pattern.
    def visitPattern(self, ctx:Python3Parser.PatternContext):
        self.myprint('visitPattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#as_pattern.
    def visitAs_pattern(self, ctx:Python3Parser.As_patternContext):
        self.myprint('visitAs_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#or_pattern.
    def visitOr_pattern(self, ctx:Python3Parser.Or_patternContext):
        self.myprint('visitOr_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#closed_pattern.
    def visitClosed_pattern(self, ctx:Python3Parser.Closed_patternContext):
        self.myprint('visitClosed_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#literal_pattern.
    def visitLiteral_pattern(self, ctx:Python3Parser.Literal_patternContext):
        self.myprint('visitLiteral_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#literal_expr.
    def visitLiteral_expr(self, ctx:Python3Parser.Literal_exprContext):
        self.myprint('visitLiteral_expr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#complex_number.
    def visitComplex_number(self, ctx:Python3Parser.Complex_numberContext):
        self.myprint('visitComplex_number')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#signed_number.
    def visitSigned_number(self, ctx:Python3Parser.Signed_numberContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#signed_real_number.
    def visitSigned_real_number(self, ctx:Python3Parser.Signed_real_numberContext):
        self.myprint('visitSigned_real_number')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#real_number.
    def visitReal_number(self, ctx:Python3Parser.Real_numberContext):
        self.myprint('visitReal_number')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#imaginary_number.
    def visitImaginary_number(self, ctx:Python3Parser.Imaginary_numberContext):
        self.myprint('visitImaginary_number')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#capture_pattern.
    def visitCapture_pattern(self, ctx:Python3Parser.Capture_patternContext):
        self.myprint('visitCapture_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#pattern_capture_target.
    def visitPattern_capture_target(self, ctx:Python3Parser.Pattern_capture_targetContext):
        self.myprint('visitPattern_capture_target')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#wildcard_pattern.
    def visitWildcard_pattern(self, ctx:Python3Parser.Wildcard_patternContext):
        self.myprint('visitWildcard_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#value_pattern.
    def visitValue_pattern(self, ctx:Python3Parser.Value_patternContext):
        self.myprint('visitValue_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#attr.
    def visitAttr(self, ctx:Python3Parser.AttrContext):
        self.myprint('visitAttr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#name_or_attr.
    def visitName_or_attr(self, ctx:Python3Parser.Name_or_attrContext):
        self.myprint('visitName_or_attr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#group_pattern.
    def visitGroup_pattern(self, ctx:Python3Parser.Group_patternContext):
        self.myprint('visitGroup_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#sequence_pattern.
    def visitSequence_pattern(self, ctx:Python3Parser.Sequence_patternContext):
        self.myprint('visitSequence_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#open_sequence_pattern.
    def visitOpen_sequence_pattern(self, ctx:Python3Parser.Open_sequence_patternContext):
        self.myprint('visitOpen_sequence_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#maybe_sequence_pattern.
    def visitMaybe_sequence_pattern(self, ctx:Python3Parser.Maybe_sequence_patternContext):
        self.myprint('visitMaybe_sequence_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#maybe_star_pattern.
    def visitMaybe_star_pattern(self, ctx:Python3Parser.Maybe_star_patternContext):
        self.myprint('visitMaybe_star_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#star_pattern.
    def visitStar_pattern(self, ctx:Python3Parser.Star_patternContext):
        self.myprint('visitStar_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#mapping_pattern.
    def visitMapping_pattern(self, ctx:Python3Parser.Mapping_patternContext):
        self.myprint('visitMapping_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#items_pattern.
    def visitItems_pattern(self, ctx:Python3Parser.Items_patternContext):
        self.myprint('visitItems_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#key_value_pattern.
    def visitKey_value_pattern(self, ctx:Python3Parser.Key_value_patternContext):
        self.myprint('visitKey_value_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#double_star_pattern.
    def visitDouble_star_pattern(self, ctx:Python3Parser.Double_star_patternContext):
        self.myprint('visitDouble_star_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#class_pattern.
    def visitClass_pattern(self, ctx:Python3Parser.Class_patternContext):
        self.myprint('visitClass_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#positional_patterns.
    def visitPositional_patterns(self, ctx:Python3Parser.Positional_patternsContext):
        self.myprint('visitPositional_patterns')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#keyword_patterns.
    def visitKeyword_patterns(self, ctx:Python3Parser.Keyword_patternsContext):
        self.myprint('visitKeyword_patterns')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#keyword_pattern.
    def visitKeyword_pattern(self, ctx:Python3Parser.Keyword_patternContext):
        self.myprint('visitKeyword_pattern')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#test.
    def visitTest(self, ctx:Python3Parser.TestContext):
        self.myprint('visitTest')
        res = self.visitChildren(ctx)
        return res


    # Visit a parse tree produced by Python3Parser#test_nocond.
    def visitTest_nocond(self, ctx:Python3Parser.Test_nocondContext):
        self.myprint('visitTest_nocond')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#lambdef.
    def visitLambdef(self, ctx:Python3Parser.LambdefContext):
        self.myprint('visitLambdef')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#lambdef_nocond.
    def visitLambdef_nocond(self, ctx:Python3Parser.Lambdef_nocondContext):
        self.myprint('visitLambdef_nocond')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#or_test.
    def visitOr_test(self, ctx:Python3Parser.Or_testContext):
        self.myprint('visitOr_test')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#and_test.
    def visitAnd_test(self, ctx:Python3Parser.And_testContext):
        self.myprint('visitAnd_test')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#not_test.
    def visitNot_test(self, ctx:Python3Parser.Not_testContext):
        self.myprint('visitNot_test')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#comparison.
    def visitComparison(self, ctx:Python3Parser.ComparisonContext):
        self.myprint('visitComparison')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#comp_op.
    def visitComp_op(self, ctx:Python3Parser.Comp_opContext):
        self.myprint('visitComp_op')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#star_expr.
    def visitStar_expr(self, ctx:Python3Parser.Star_exprContext):
        self.myprint('visitStar_expr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#expr.
    def visitExpr(self, ctx:Python3Parser.ExprContext):
        self.myprint('visitExpr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#atom_expr.
    def visitAtom_expr(self, ctx:Python3Parser.Atom_exprContext):
        res = self.visitChildren(ctx)
        return res

    # Visit a parse tree produced by Python3Parser#atom.
    def visitAtom(self, ctx:Python3Parser.AtomContext):
        self.myprint('visitAtom')
        if ctx.NUMBER() != None:
            return ctx.NUMBER().getText()
        elif ctx.name() != None:
            return ctx.name().getText()
        elif ctx.STRING(0) != None:
            return ctx.STRING(0)
        elif ctx.NONE() != None:
            return "None"
        elif ctx.TRUE() != None:
            return "True"
        elif ctx.FALSE() != None:
            return "False"
        else:
            return 'not_supported'

    # Visit a parse tree produced by Python3Parser#name.
    def visitName(self, ctx:Python3Parser.NameContext):
        self.myprint('visitName')
        return ctx.NAME().getText()

    # Visit a parse tree produced by Python3Parser#testlist_comp.
    def visitTestlist_comp(self, ctx:Python3Parser.Testlist_compContext):
        self.myprint('visitTestlist_comp')
        res = self.visitChildren(ctx)
        return res

    # Visit a parse tree produced by Python3Parser#trailer.
    def visitTrailer(self, ctx:Python3Parser.TrailerContext):
        self.myprint('visitTrailer')
        return self.visitChildren(ctx)

    # Visit a parse tree produced by Python3Parser#subscriptlist.
    def visitSubscriptlist(self, ctx:Python3Parser.SubscriptlistContext):
        self.myprint('visitSubscriptlist')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#subscript_.
    def visitSubscript_(self, ctx:Python3Parser.Subscript_Context):
        self.myprint('visitSubscript_')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#sliceop.
    def visitSliceop(self, ctx:Python3Parser.SliceopContext):
        self.myprint('visitSliceop')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#exprlist.
    def visitExprlist(self, ctx:Python3Parser.ExprlistContext):
        self.myprint('visitExprlist')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#testlist.
    def visitTestlist(self, ctx:Python3Parser.TestlistContext):
        assert ctx.getChildCount() == 1
        res = ctx.getChild(0).getText()
        return res


    # Visit a parse tree produced by Python3Parser#dictorsetmaker.
    def visitDictorsetmaker(self, ctx:Python3Parser.DictorsetmakerContext):
        self.myprint('visitDictorsetmaker')
        return self.visitChildren(ctx)

    
    # Visit a parse tree =produced by Python3Parser#classdef.
    def visitClassdef(self, ctx:Python3Parser.ClassdefContext):
        self.myprint('visitClassdef ')
        res = ""
        obj_dict = {}  # dictionary of (class x object) definitions
        class_name = ctx.name().getText()
        if class_name == "Context":
            fresh_obj = FreshConst(IntSort(),prefix="obj")
            fresh_str = str(fresh_obj).replace("!","")
            res += fresh_str+"=BContext()\n"
            obj_dict[class_name] = fresh_str
            block = self.visitBlock(ctx.block())
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removes leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removes trailing spaces
            block = re.sub(r"\b%s\b"%'self\.',fresh_str+"_",block)
            block = re.sub(r"\b%s\b"%'selF',fresh_str,block)
            res = res + block
        elif class_name.startswith('Machine_'):
            fresh_obj = FreshConst(IntSort(),prefix="obj")
            fresh_str = str(fresh_obj).replace("!","")
            obj_dict[class_name] = fresh_str
            block = self.visitBlock(ctx.block())
            
            block = re.sub(r"^\s+", "", block, flags=re.UNICODE) # removes leading spaces
            block = re.sub(r"\s+$", "", block, flags=re.UNICODE) # removes trailing spaces            
            # negative lookahead -
            # it replaces 'self.' with 'fresh_str_' as long as 'self.' is NOT suceeded by 'context'
            block = re.sub(r"\b%s(?!context)\b"%'self\.',fresh_str+"_",block) 
            # it replaces 'self' with 'fresh_str_' as long as 'self.' is NOT suceeded by 'context'
            block = re.sub(r"\b%s(?!.context)\b"%'self',fresh_str,block)
            # it replaces selF with fresh_str            
            block = re.sub(r"\b%s\b"%'selF',fresh_str,block)            
            # it replaces 'self.content=' with 'obj_context='
            block = re.sub(r"\b%s\b"%'self\.context\=',fresh_str+'_context=',block)

           
            super_class_name = ctx.arglist().getText()
            if super_class_name != 'object':
                # initial handling of calls to 'super().event_aaa()'
                # the final handling is accomplished by visitFile_input
                pattern1 = r'(super\(\).)(ref_event_|event_)(.*?)(\(\))'
                # it replaces 'super()' with 'super_class_name.', and it removes (), then
                replacement1 = r'%s.\2\3'%super_class_name
                block = re.sub(pattern1, replacement1, block)
                
                # initial handling of super().__init__(aaa.bbb)
                pattern2 = '(super\(\).)(__init__)\(([a-zA-Z0-9_.,]+)\)'
                # '(class_name,super_class_name).__init__'
                replacement2 = r'(%s:%s).\2'%(class_name,super_class_name)
                block = re.sub(pattern2, replacement2, block)

                ###
            res = res + block
        return res, obj_dict
    

    # Visit a parse tree produced by Python3Parser#arglist.
    def visitArglist(self, ctx:Python3Parser.ArglistContext):
        self.myprint('visitArglist')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#argument.
    def visitArgument(self, ctx:Python3Parser.ArgumentContext):
        self.myprint('visitArgument')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#comp_iter.
    def visitComp_iter(self, ctx:Python3Parser.Comp_iterContext):
        self.myprint('visitComp_iter')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#comp_for.
    def visitComp_for(self, ctx:Python3Parser.Comp_forContext):
        self.myprint('visitComp_for')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#comp_if.
    def visitComp_if(self, ctx:Python3Parser.Comp_ifContext):
        self.myprint('visitComp_if')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#encoding_decl.
    def visitEncoding_decl(self, ctx:Python3Parser.Encoding_declContext):
        self.myprint('visitEncoding_decl')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#yield_expr.
    def visitYield_expr(self, ctx:Python3Parser.Yield_exprContext):
        self.myprint('visitYield_expr')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#yield_arg.
    def visitYield_arg(self, ctx:Python3Parser.Yield_argContext):
        self.myprint('visitYield_arg')
        return self.visitChildren(ctx)


    # Visit a parse tree produced by Python3Parser#strings.
    def visitStrings(self, ctx:Python3Parser.StringsContext):
        self.myprint('visitStrings')
        return self.visitChildren(ctx)


    

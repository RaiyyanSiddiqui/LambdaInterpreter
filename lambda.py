import re

class Lamb:
    showDisambiguationInString = False
    simplifyLambdaInString = True
    showRawRename = True
    sessionUniqueId = 0
    def __init__(self, paramsOrOther = None, body = None, parent = None):
        if isinstance(paramsOrOther, str):
            self.__init__(Lamb.compileLambda(paramsOrOther)) # calls copy constructor from compiled lambda
        elif isinstance(paramsOrOther, Lamb): # copy constructor
            self.params = paramsOrOther.params[:]
            self.body = []
            for x in paramsOrOther.body:
                if isinstance(x, Lamb):
                    self.body.append(Lamb(x))
                else:
                    self.body.append(x)
            self.parent = parent
            self.isBracket = paramsOrOther.isBracket
        else: # initialization / default constructor
            self.params = [] if paramsOrOther == None else paramsOrOther
            self.body = [] if body == None else body
            self.parent = parent
            self.isBracket = len(self.params) == 0
        self.rename()
    def clone(self):
        """cpy = Lamb(self.params[:], self.body[:])
        for idx in range(len(cpy.body)):
            if isinstance(cpy.body[idx],Lamb):
                cpy.body[idx] = cpy.body[idx].clone()
        return cpy"""
        return Lamb(self)
    
    # remove $num rename disambiguation
    # if no special $num is attached, it just returns the same name back
    @staticmethod
    def removeRename(name):
        return name.split('$')[0]
    #recursive
    def rename(self, params = None):
        if params == None:
            params = {}
        for pIdx, pVal in enumerate(self.params):
            updateString = '$' + str(Lamb.sessionUniqueId)
            Lamb.sessionUniqueId += 1
            
            params.update({pVal : Lamb.removeRename(pVal) + updateString})
            self.params[pIdx] = Lamb.removeRename(pVal) + updateString
        for bIdx, bVal in enumerate(self.body):
            if isinstance(bVal, Lamb):
                bVal.rename(params)
            elif params.get(bVal) != None: #must be string
                self.body[bIdx] = params.get(bVal)
    def __str__(self):
        out = '' #if not self.isBracket else 'B' 
        
        if(len(self.params) > 0 or not Lamb.simplifyLambdaInString):
            out += '{\\'
            for p in self.params:
                out += (p if Lamb.showDisambiguationInString else Lamb.removeRename(p)) + " "
            out += " -> "
        else:
            out += '(' 
        for b in self.body:
            out += ( str(b) if Lamb.showDisambiguationInString else Lamb.removeRename(str(b)) ) + " "
        out += "}" if(len(self.params) > 0 or not Lamb.simplifyLambdaInString) else ')'
        return out
    def __repr__(self):
        return self.__str__()
    
    def functionalEquivalence(self, other, sParamScope = None, oParamScope = None):
        def findIndex(scope, item):
            for scIdx, sc in enumerate(scope):
                try:
                    index_element = sc.index(item)
                    return (scIdx, index_element)
                except ValueError:
                    continue
            return None
        # clone
        newSelf = Lamb(self)
        newOther = Lamb(other)
        
        
        
        if sParamScope == None:
            newSelf.simplify()
            newOther.simplify()
            sParamScope = [newSelf.params[:]]
            oParamScope = [newOther.params[:]]
        else:
            sParamScope += newSelf.params[:]
            oParamScope += newOther.params[:]
            
        if len(newSelf.params) != len(newOther.params):
            return False
        if len(newSelf.body) != len(newOther.body):
            return False
        for idx in range(len(newSelf.body)):
            selfItem = newSelf.body[idx]
            otherItem = newOther.body[idx]
            
            if isinstance(selfItem, Lamb) and isinstance(otherItem, Lamb):
                if not selfItem.functionalEquivalence(otherItem, sParamScope[:], oParamScope[:]):# copy magic, no need to copy inners
                    return False
            elif isinstance(selfItem, str) and isinstance(otherItem, str):
                #oh boy
                selfParamIdx = findIndex(sParamScope, selfItem)
                otherParamIdx = findIndex(oParamScope, otherItem)
                if selfParamIdx == None and otherParamIdx == None:
                    if selfItem != otherItem:
                        return False
                elif selfParamIdx == None or otherParamIdx == None:
                    return False
                elif (selfParamIdx[0] != otherParamIdx[0]) or (selfParamIdx[1] != otherParamIdx[1]):
                    return False
            else:
                return False
        return True
    
    # change all possible strings into their matching lambda definitions if applicable
    # non matches in the body stay as strings
    # NONRECURSIVE DEFINITIONS: potential recursive pre-function
    # if recursive definitions allowed, then this must be in the loop
    # recursion NOT Allowed normally
    def expandDefinitions(self, definitions, recur = True):
        #print(self)
        for bIdx, bVal in enumerate(self.body):
            # .get() returns None when no match found
            # assigns GET to "matchingLambda" if found
            matching = definitions.get(bVal)
            if isinstance(bVal, str) and matching != None: 
                if isinstance(matching, Lamb):
                    self.body[bIdx] =  matching.clone()
                else:
                    self.body[bIdx] = matching
            if isinstance(self.body[bIdx], Lamb):
                self.body[bIdx].expandDefinitions(definitions, True)
    #update
    def __call__(self, *args):
        argIdx = 0 # iter
        changed = False
        definitions = {}
        #!print("StartCall", self, args)
        #self.rename(self.id)
        while len(self.params) > 0:
            # ran out of arguments while params not fully satisfied
            if argIdx == len(args):
               #!print("noArgsCall")
               return (argIdx > 0, [self])
            #print('loop', idx, '--', self.body, args)
            param = self.params.pop(0)
            
            arg = args[argIdx]
            if(isinstance(arg, Lamb)):
                arg.rename()
                _ = True
            #print('renamed', arg)
            definitions.update({param : arg})
            # nested not
            # if nested elif after isinstance must be used
            self.expandDefinitions(definitions)
            argIdx += 1
        # destroys lambda
        #return (True, self.body + list(args)[argIdx:]) # temp
        #print("APPLY", self, args, 'bodylen',len(self.body), 'isbracket', self.isBracket)
        if self.isBracket and len(self.body) >= 2:
            #!print("necessaryBracketCall", argIdx)
            return (argIdx > 0, [self] + list(args)[argIdx:])
        else:
            #!print("decomposeCall")
            return (True, self.body + list(args)[argIdx:])
    #weird operator precedence
    def staticEval(self, definitions, sequential = True, debug = False, depth = 0):
        # try going opposite
        #!print("STARTeval", self)
        turn = 0
        startingIdx = 0
        #self.rename()
        self.expandDefinitions(definitions)
        startingIdx = 0
        
        changedSingleTurn = True
        changedAtAll = False
        
        #self.rename()
       #!print(self.body)
        while len(self.body) > 0 and startingIdx < len(self.body) and changedSingleTurn:
            changedSingleTurn = False
            #!print("Sequential IDX: ", startingIdx)
        # move onto next if sequential eval
                # if it keeps encountering strings, continue until it doesn't
            simplifyChanged = self.simplify()
            changedSingleTurn = changedSingleTurn or simplifyChanged
            while startingIdx < len(self.body) and isinstance(self.body[startingIdx], str) :
                if not sequential: return False
                startingIdx += 1
                continue
            if startingIdx == len(self.body):
                #!print(startingIdx, self.body)
                #!print('reached end')
                return changedSingleTurn or changedAtAll
            #guaranteed to be a lambda
           #!print('debugEval: ', 'startidx', startingIdx, self)
            #self.body[startingIdx].staticEval(definitions, sequential, debug)
               
            (applyChanged, newBody) = self.body[startingIdx].__call__(*self.body[startingIdx + 1 : ])
            self.body = self.body[:startingIdx] + newBody
            changedSingleTurn = changedSingleTurn or applyChanged
            
            if isinstance(self.body[startingIdx], Lamb):
                recurChanged = self.body[startingIdx].staticEval(definitions, sequential, debug, depth + 1)
                #!print('recurChanged', recurChanged)
                changedSingleTurn = changedSingleTurn or recurChanged
            # debug print 
            if(debug):
                print('\nDepth:', depth, 'TurnEval:', turn, 'startingIdx', startingIdx, '--', self)
            # no need to update changed at all, since singleTurn is defininitionally false
            if not changedSingleTurn: 
                break;
            changedAtAll = changedAtAll or changedSingleTurn
            turn += 1
        
        
        finalSimp = self.simplify()
        #!print(self,'done\n', 'turn',turn, 'sidx', startingIdx, 'len', len(self.body), 'changed', changedAtAll, 'finalSimp', finalSimp)
        return changedAtAll or finalSimp
        
    def simplify(self):
        # inner lambda
        #print('simp', self)
        #!print('simpStart')
        changed = False
        while len(self.body) == 1 and isinstance(self.body[0], Lamb):
            #!print('doSimp')
            inner = self.body[0]
            self.params += inner.params
            self.body = inner.body
            #print('recosimp',self)
            changed = True
        for b in self.body:
            if isinstance(b, Lamb):
                res = b.simplify()
                changed = changed or res
        return changed
    # returns lambda
    # strongly binding, left aligned
    @classmethod
    def lexLambda(cls, text):
        modified_text = text.replace('{','')
        modified_text = modified_text.replace('}','')
        modified_text = modified_text.replace('->','.')
        modified_text = modified_text.replace('=>','.')
        words = re.split(r'([ ().\\])', modified_text.strip())
        tokens = []
        for word in words:
            if word.strip() != '':
                tokens.append(word.strip())
        return tokens
    
    # assume properly formed line
    @classmethod
    def compileLambda(cls, text):
        tokens = cls.lexLambda(text)
        lState = 'args'
        root = Lamb()
        #print(tokens)
        try:
            for t in tokens:
                #print(t)
                if(t == '('):
                    new_root = Lamb([], [], root)
                    root.body.append(new_root)
                    root = new_root # capture root by reference
                    lState = 'body'
                elif(t == ')'):
                    root = root.parent
                    #lState = 'body' ## no bracket in args normally 
                elif(t == '\\'): # create new lambda
                    # if empty parenthesis, it's redundant when creating a new lambda
                    # eg. (\ a b c . d) everything after d is a part of abc
                    # counterexample (stringword \ d . f) parenthesis required
                    if len(root.params) == 0 and len(root.body) == 0 and root.parent != None:
                        pass
                    else:                    
                        new_root = Lamb([], [], root)
                        root.body.append(new_root)
                        root = new_root # capture root by reference
                    lState = 'params'
                elif (t == '.'):
                    lState = 'body'
                elif(lState == 'params'):
                    #print('params')
                    #print(root)
                    root.params.append(t)
                elif (lState == 'body'):
                    #print('body')
                    #print(root)
                    root.body.append(t)
            while root.parent != None:
                root = root.parent
            # or the root ## WILL CHANGE
            return root.body[0]
        except:
            print("ERROR: compiling lambda.")
            return Lamb()
            
            
class LambInterpreter:
    demo_definitions = {
        "true"   : Lamb(r'\a b -> a'),
        "false"  : Lamb(r'\a b -> b'),
        "0"      : Lamb(r'\f x -> x'),
        "1"      : Lamb(r'\f x -> f x'),
        "2"      : Lamb(r'\f x -> f (f x)'),
        "3"      : Lamb(r'\f x -> f(f(f x))'),
        "4"      : Lamb(r'\f x -> f(f(f(f x)))'),
        "5"      : Lamb(r'\f x -> f(f(f(f(f x))))'),
        "6"      : Lamb(r'\f x -> f(f(f(f(f(f x)))))'),
        "7"      : Lamb(r'\f x -> f(f(f(f(f(f(f x))))))'),
        "8"      : Lamb(r'\f x -> f(f(f(f(f(f(f(f x)))))))'),
        "9"      : Lamb(r'\f x -> f(f(f(f(f(f(f(f(f x))))))))'),
        "10"     : Lamb(r'\f x -> f(f(f(f(f(f(f(f(f(f x)))))))))'),
        
        "iszero" : Lamb(r'\n -> n (\z -> false) true'),
        "succ"   : Lamb(r'\n f x -> f (n f x)'),
        "pred"   : Lamb(r'\n f x -> n (\g h -> h (g f)) (\u -> x) (\u -> u)'),
        
        "add"    : Lamb(r'\m n f x -> m f (n f x)'),
        "mul"    : Lamb(r'\m n f x -> m (n f) x'),
        
        "Ycomb"  : Lamb(r'\f -> (\x -> f(x x))(\x -> f(x x))') 
    }
    def __init__(self):
        Lamb.sessionUniqueId = 0
        self.sessionOutput = ""
        self.sessionDefinitions = {}
    
    def clearSession(self):
        self.sessionDefinitions = {}
        self.sessionOutput = ''
        Lamb.sessionUniqueId = 0
        
        for k, v in self.demo_definitions.items():
            self.sessionDefinitions[k] = Lamb(v)
        self.resetRename()
        
    # returns definition list as well as a string containing the result    
    def saveSession(self):
        return (dict(self.sessionDefinitions), self.sessionOutput + "", Lamb.sessionUniqueId)

    def loadSession(self, sessionInfo):
        self.sessionDefinitions = sessionInfo[0]
        self.sessionOutput = sessionInfo[1]
        Lamb.sessionUniqueId = sessionInfo[2]
    def resetRename(self):
        Lamb.sessionUniqueId = 0
        for k, v in self.sessionDefinitions.items():
            v.rename()
            self.sessionDefinitions[k] = v
    def interpret(self, text):
        def cleanSplit(text, pattern):
            return [t.strip() for t in text.split(pattern) if t.strip() != '']
        out = ''
        modified_text = text.replace('{','')
        modified_text = modified_text.replace('}','')
        modified_text = modified_text.replace('->','.')
        modified_text = modified_text.replace('=>','.')
        modified_text = modified_text.replace('==','~')
        lines = cleanSplit(modified_text, '\n')
        #print(lines)
        # TODO add comparison
        for line in lines:
            
            eq = cleanSplit(line, '=')
            # final item, whether it's a assignment statement (a = \db.c), or an expression \f. succ 1
            l = r'\ ->' + eq[-1] # dummy parent
            #print(l)
            result = Lamb(l) 
            #print(result)
            #print(result)
            result.staticEval(self.sessionDefinitions) # can't
            result.simplify()
            
            for k, v in self.sessionDefinitions.items():
                if v.functionalEquivalence(result):
                    print("EQUIVALENT TO", k)
                    
            if len(eq) == 2:
                self.sessionDefinitions.update({eq[0] : result})
                out += eq[0] + " = "
            if len(result.params) == 0:
                for r in result.body:
                    out += str(r) + " "
            else:
                out += str(result)
            
                
            out += '\n'
            
        self.sessionOutput += out
        return out
    
    def interpreter_console(self):
        inp = 'help'
        print('Lambda Calculus Interpreter')
        print('   by Raiyyan Siddiqui')
        print('Type \'help\' to see a list of commands')
        
        self.clearSession()
        while(True):
            """for k, v in self.demo_definitions.items():
                print(k, ':', v)"""
            if(inp.strip() != ''): 
                print()
                print('-*' * 30)
                print("Enter phrase to evaluate")
            inp = input(">>")
            if(inp == 'exit'):
                break
            elif (inp == 'help'):
                print("""
HELP - LIST OF USEFUL COMMANDS
-- exit - exits the program
-- help - prints all available commands
-- clear - clears all previous session info
-- settings - toggles lambda output modes
                      
-- Reserved strings: {, }, (, ), , \\, =, ==, ~, ->, =>, ., \\n 
-- Lambda Statement, 2 formats:
--    CONST = LAMBDA_EXPRESSION // saves expression to constant
--    LAMBDA_EXPRESSION         // doesn't save result
-- Lambda Expression : 
--    brackets, constants(assigned from before, can be lambdas or others themselves),
--     lambdas, and strings
--    eg. (\\f x -> x)(f false)
""")
            elif(inp == 'clear'):
                self.clearSession()
            elif (inp == 'demo'): # deprecated
                print("-- PLACEHOLDER")
            elif(inp == 'settings'):
                settingsInp = ''
                while(settingsInp != 'e'):
                    print("-- (d)isambiguated/renamed names shown = ", Lamb.showDisambiguationInString)
                    print("-- (s)implified lambda print format = ", Lamb.simplifyLambdaInString)
                    print('-- Type d or s to toggle either, and e to exit')
                    settingsInp = input(">>")
                    if(settingsInp == 'd'):
                        Lamb.showDisambiguationInString = not Lamb.showDisambiguationInString
                    elif(settingsInp == 's'):
                        Lamb.simplifyLambdaInString = not Lamb.simplifyLambdaInString
                    print("--" * 30)
            elif (inp.strip() == ''):
                pass
            else:
                print('--', self.interpret(inp))
                self.resetRename()



if __name__ == '__main__':
    l = LambInterpreter()
    l.interpreter_console()

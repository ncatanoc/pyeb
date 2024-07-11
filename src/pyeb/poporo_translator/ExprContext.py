

    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def atom_expr(self):
            return self.getTypedRuleContext(Python3Parser.Atom_exprContext,0)


        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(Python3Parser.ExprContext)
            else:
                return self.getTypedRuleContext(Python3Parser.ExprContext,i)


        def ADD(self, i:int=None):
            if i is None:
                return self.getTokens(Python3Parser.ADD)
            else:
                return self.getToken(Python3Parser.ADD, i)

        def MINUS(self, i:int=None):
            if i is None:
                return self.getTokens(Python3Parser.MINUS)
            else:
                return self.getToken(Python3Parser.MINUS, i)

        def NOT_OP(self, i:int=None):
            if i is None:
                return self.getTokens(Python3Parser.NOT_OP)
            else:
                return self.getToken(Python3Parser.NOT_OP, i)

        def POWER(self):
            return self.getToken(Python3Parser.POWER, 0)

        def STAR(self):
            return self.getToken(Python3Parser.STAR, 0)

        def AT(self):
            return self.getToken(Python3Parser.AT, 0)

        def DIV(self):
            return self.getToken(Python3Parser.DIV, 0)

        def MOD(self):
            return self.getToken(Python3Parser.MOD, 0)

        def IDIV(self):
            return self.getToken(Python3Parser.IDIV, 0)

        def LEFT_SHIFT(self):
            return self.getToken(Python3Parser.LEFT_SHIFT, 0)

        def RIGHT_SHIFT(self):
            return self.getToken(Python3Parser.RIGHT_SHIFT, 0)

        def AND_OP(self):
            return self.getToken(Python3Parser.AND_OP, 0)

        def XOR(self):
            return self.getToken(Python3Parser.XOR, 0)

        def OR_OP(self):
            return self.getToken(Python3Parser.OR_OP, 0)

        def getRuleIndex(self):
            return Python3Parser.RULE_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExpr" ):
                listener.enterExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExpr" ):
                listener.exitExpr(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitExpr" ):
                return visitor.visitExpr(self)
            else:
                return visitor.visitChildren(self)



    def expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = Python3Parser.ExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 194
        self.enterRecursionRule(localctx, 194, self.RULE_expr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 1154
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [3, 4, 10, 20, 30, 31, 38, 40, 45, 55, 57, 64, 77]:
                self.state = 1147
                self.atom_expr()
                pass
            elif token in [71, 72, 76]:
                self.state = 1149 
                self._errHandler.sync(self)
                _alt = 1
                while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                    if _alt == 1:
                        self.state = 1148
                        _la = self._input.LA(1)
                        if not(((((_la - 71)) & ~0x3f) == 0 and ((1 << (_la - 71)) & 35) != 0)):
                            self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()

                    else:
                        raise NoViableAltException(self)
                    self.state = 1151 
                    self._errHandler.sync(self)
                    _alt = self._interp.adaptivePredict(self._input,146,self._ctx)

                self.state = 1153
                self.expr(7)
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 1179
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,149,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 1177
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,148,self._ctx)
                    if la_ == 1:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1156
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 1157
                        self.match(Python3Parser.POWER)
                        self.state = 1158
                        self.expr(9)
                        pass

                    elif la_ == 2:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1159
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 1160
                        _la = self._input.LA(1)
                        if not(((((_la - 56)) & ~0x3f) == 0 and ((1 << (_la - 56)) & 1074659329) != 0)):
                            self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 1161
                        self.expr(7)
                        pass

                    elif la_ == 3:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1162
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 1163
                        _la = self._input.LA(1)
                        if not(_la==71 or _la==72):
                            self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 1164
                        self.expr(6)
                        pass

                    elif la_ == 4:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1165
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 1166
                        _la = self._input.LA(1)
                        if not(_la==69 or _la==70):
                            self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 1167
                        self.expr(5)
                        pass

                    elif la_ == 5:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1168
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 1169
                        self.match(Python3Parser.AND_OP)
                        self.state = 1170
                        self.expr(4)
                        pass

                    elif la_ == 6:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1171
                        if not self.precpred(self._ctx, 2):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                        self.state = 1172
                        self.match(Python3Parser.XOR)
                        self.state = 1173
                        self.expr(3)
                        pass

                    elif la_ == 7:
                        localctx = Python3Parser.ExprContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                        self.state = 1174
                        if not self.precpred(self._ctx, 1):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 1)")
                        self.state = 1175
                        self.match(Python3Parser.OR_OP)
                        self.state = 1176
                        self.expr(2)
                        pass

             
                self.state = 1181
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,149,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class Atom_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def atom(self):
            return self.getTypedRuleContext(Python3Parser.AtomContext,0)


        def AWAIT(self):
            return self.getToken(Python3Parser.AWAIT, 0)

        def trailer(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(Python3Parser.TrailerContext)
            else:
                return self.getTypedRuleContext(Python3Parser.TrailerContext,i)


        def getRuleIndex(self):
            return Python3Parser.RULE_atom_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAtom_expr" ):
                listener.enterAtom_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAtom_expr" ):
                listener.exitAtom_expr(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAtom_expr" ):
                return visitor.visitAtom_expr(self)
            else:
                return visitor.visitChildren(self)




    def atom_expr(self):

        localctx = Python3Parser.Atom_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 196, self.RULE_atom_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 1183
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==10:
                self.state = 1182
                self.match(Python3Parser.AWAIT)


            self.state = 1185
            self.atom()
            self.state = 1189
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,151,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 1186
                    self.trailer() 
                self.state = 1191
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,151,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


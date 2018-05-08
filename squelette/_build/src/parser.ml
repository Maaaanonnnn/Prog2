
module MenhirBasics = struct
  
  exception Error
  
  type token = Tokens.token
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState107
  | MenhirState102
  | MenhirState99
  | MenhirState98
  | MenhirState93
  | MenhirState89
  | MenhirState87
  | MenhirState84
  | MenhirState82
  | MenhirState81
  | MenhirState79
  | MenhirState77
  | MenhirState73
  | MenhirState70
  | MenhirState68
  | MenhirState65
  | MenhirState62
  | MenhirState60
  | MenhirState58
  | MenhirState56
  | MenhirState54
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState45
  | MenhirState40
  | MenhirState39
  | MenhirState36
  | MenhirState31
  | MenhirState30
  | MenhirState29
  | MenhirState26
  | MenhirState24
  | MenhirState21
  | MenhirState18
  | MenhirState14
  | MenhirState12
  | MenhirState6
  | MenhirState3
  | MenhirState0

# 1 "src/parser.mly"
  
    open Ast

    let rec mk_lam ps t =
        match ps with
        | [] -> t
        | (x,None)::ps' -> fst x, Lam(snd x, None, mk_lam ps' t)
        | (x,Some ty)::ps' -> fst x, Lam(snd x, (Some ty), mk_lam ps' t)


# 76 "src/parser.ml"

let rec _menhir_goto_cmd : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.cmd Ast.loc) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.LET ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | Tokens.EOF ->
        _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack) MenhirState107
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107

and _menhir_goto_letexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 97 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState73
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 150 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 154 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 158 "src/parser.ml"
        ))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 167 "src/parser.ml"
        ) = 
# 129 "src/parser.mly"
        ( fst id, LetIn(snd id, (fst t, Fix(fst id, Lam(snd id, None, t))), u) )
# 171 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState79
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 222 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 226 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 230 "src/parser.ml"
        ))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 239 "src/parser.ml"
        ) = 
# 131 "src/parser.mly"
        ( fst id, LetIn(snd id, (fst t, Fix(mk_lam ((id, None)::ps) t)), u) )
# 243 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState84
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 294 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 298 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 302 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 310 "src/parser.ml"
        ) = 
# 125 "src/parser.mly"
        ( fst id, LetIn(snd id, t,u)  )
# 314 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState89
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 365 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 369 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 373 "src/parser.ml"
        ))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 381 "src/parser.ml"
        ) = 
# 127 "src/parser.mly"
        ( fst id, LetIn(snd id, mk_lam ps t,u)  )
# 385 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState93
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93)
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 431 "src/parser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 438 "src/parser.ml"
            ) = 
# 84 "src/parser.mly"
       ( e )
# 442 "src/parser.ml"
             in
            _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (el : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 463 "src/parser.ml"
            ))), _, (er : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 467 "src/parser.ml"
            ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 475 "src/parser.ml"
            ) = 
# 86 "src/parser.mly"
      ( fst el, Pair(el,er) )
# 479 "src/parser.ml"
             in
            _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 494 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 498 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 146 "src/parser.mly"
        ( fst id, LetRec(snd id, None, mk_lam ps t) )
# 506 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 515 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 519 "src/parser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 142 "src/parser.mly"
        ( fst id, Let(snd id, None, t) )
# 526 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 535 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 539 "src/parser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 144 "src/parser.mly"
        ( fst id, Let(snd id, None, mk_lam ps t) )
# 546 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_funexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 555 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 566 "src/parser.ml"
        ))), _, (ty : (
# 42 "src/parser.mly"
      (ty)
# 570 "src/parser.ml"
        ))), _, (t : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 574 "src/parser.ml"
        ))) = _menhir_stack in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 584 "src/parser.ml"
        ) = 
# 119 "src/parser.mly"
        ( fst id, Lam(snd id, (Some ty), t) )
# 588 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 597 "src/parser.ml"
        ))), _, (t : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 601 "src/parser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 608 "src/parser.ml"
        ) = 
# 117 "src/parser.mly"
        ( fst id, Lam(snd id, None, t) )
# 612 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState70
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState70
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState70
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState70
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState70
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (cond : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 701 "src/parser.ml"
        ))), _, (l : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 705 "src/parser.ml"
        ))), _, (r : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 709 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 717 "src/parser.ml"
        ) = 
# 115 "src/parser.mly"
        ( fst cond, Ite(cond,l,r) )
# 721 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState102 | MenhirState99 | MenhirState21 | MenhirState26 | MenhirState93 | MenhirState87 | MenhirState89 | MenhirState82 | MenhirState84 | MenhirState77 | MenhirState79 | MenhirState30 | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (s : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 730 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 735 "src/parser.ml"
        ) = 
# 123 "src/parser.mly"
        ( s )
# 739 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run45 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 748 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState45
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState45
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState45
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45

and _menhir_run50 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 778 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_run54 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 808 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54

and _menhir_run56 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 838 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56

and _menhir_run58 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 868 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState58
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState58
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState58
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58

and _menhir_run52 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 898 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52

and _menhir_run62 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 928 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState62
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62

and _menhir_run12 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 42 "src/parser.mly"
      (ty)
# 958 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.BOOL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | Tokens.INT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState12
    | Tokens.TYID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
    | Tokens.UNIT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12

and _menhir_run14 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 42 "src/parser.mly"
      (ty)
# 980 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.BOOL ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | Tokens.INT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | Tokens.TYID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _v
    | Tokens.UNIT _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14

and _menhir_goto_binopexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1002 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState102 | MenhirState99 | MenhirState21 | MenhirState26 | MenhirState93 | MenhirState87 | MenhirState89 | MenhirState82 | MenhirState84 | MenhirState77 | MenhirState79 | MenhirState30 | MenhirState73 | MenhirState31 | MenhirState68 | MenhirState70 | MenhirState65 | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.AND ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState60
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState60
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState60
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60)
        | Tokens.GT ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.OR ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.IN | Tokens.LET | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (s : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1056 "src/parser.ml"
            ))) = _menhir_stack in
            let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 1061 "src/parser.ml"
            ) = 
# 113 "src/parser.mly"
        ( s )
# 1065 "src/parser.ml"
             in
            _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1080 "src/parser.ml"
        ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1084 "src/parser.ml"
        ))) = _menhir_stack in
        let _10 = () in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1090 "src/parser.ml"
        ) = let b =
          let _1 = _10 in
          
# 68 "src/parser.mly"
    ( Times )
# 1096 "src/parser.ml"
          
        in
        
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1102 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1119 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1123 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1129 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 64 "src/parser.mly"
    ( Plus )
# 1135 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1141 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1156 "src/parser.ml"
        ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1160 "src/parser.ml"
        ))) = _menhir_stack in
        let _10 = () in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1166 "src/parser.ml"
        ) = let b =
          let _1 = _10 in
          
# 70 "src/parser.mly"
    ( Div )
# 1172 "src/parser.ml"
          
        in
        
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1178 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1201 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1205 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1211 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 74 "src/parser.mly"
    ( Or )
# 1217 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1223 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1246 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1250 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1256 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 66 "src/parser.mly"
    ( Minus )
# 1262 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1268 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1295 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1299 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1305 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 78 "src/parser.mly"
    ( Gt )
# 1311 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1317 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.AND ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.OR ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1350 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1354 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1360 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 76 "src/parser.mly"
    ( Eq )
# 1366 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1372 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run58 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1401 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1405 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1411 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 72 "src/parser.mly"
    ( And )
# 1417 "src/parser.ml"
              
            in
            
# 110 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1423 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_param_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (((Utils.loc * Ast.var) * Ast.ty option) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : ((Utils.loc * Ast.var) * Ast.ty option))), _, (xs : (((Utils.loc * Ast.var) * Ast.ty option) list))) = _menhir_stack in
        let _v : (((Utils.loc * Ast.var) * Ast.ty option) list) = 
# 197 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 1446 "src/parser.ml"
         in
        _menhir_goto_nonempty_list_param_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState21
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState102
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 42 "src/parser.mly"
      (ty)
# 1623 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 1642 "src/parser.ml"
            ))), _, (ty : (
# 42 "src/parser.mly"
      (ty)
# 1646 "src/parser.ml"
            ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : ((Utils.loc * Ast.var) * Ast.ty option) = 
# 138 "src/parser.mly"
        (id, Some ty)
# 1654 "src/parser.ml"
             in
            _menhir_goto_param _menhir_env _menhir_stack _menhir_s _v
        | Tokens.TIMES ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR | Tokens.TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (tl : (
# 42 "src/parser.mly"
      (ty)
# 1677 "src/parser.ml"
            ))), _, (tr : (
# 42 "src/parser.mly"
      (ty)
# 1681 "src/parser.ml"
            ))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 42 "src/parser.mly"
      (ty)
# 1687 "src/parser.ml"
            ) = 
# 58 "src/parser.mly"
    ( TyTimes(tl,tr) )
# 1691 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR | Tokens.TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (tl : (
# 42 "src/parser.mly"
      (ty)
# 1712 "src/parser.ml"
            ))), _, (tr : (
# 42 "src/parser.mly"
      (ty)
# 1716 "src/parser.ml"
            ))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 42 "src/parser.mly"
      (ty)
# 1722 "src/parser.ml"
            ) = 
# 56 "src/parser.mly"
    ( TyArrow(tl,tr) )
# 1726 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.ARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Tokens.FALSE _v ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
                | Tokens.FST ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | Tokens.FUN ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | Tokens.ID _v ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
                | Tokens.IF ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | Tokens.LEFTPAR ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | Tokens.NUM _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
                | Tokens.SND ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState39
                | Tokens.TRUE _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
                | Tokens.UNIT _v ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | Tokens.TIMES ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_appexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1796 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.AND | Tokens.COMMA | Tokens.DIV | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN | Tokens.TIMES ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (s : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1821 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1826 "src/parser.ml"
        ) = 
# 108 "src/parser.mly"
        ( s )
# 1830 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_param : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Utils.loc * Ast.var) * Ast.ty option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.ID _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | Tokens.LEFTPAR ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.EQUAL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : ((Utils.loc * Ast.var) * Ast.ty option))) = _menhir_stack in
        let _v : (((Utils.loc * Ast.var) * Ast.ty option) list) = 
# 195 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 1860 "src/parser.ml"
         in
        _menhir_goto_nonempty_list_param_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 1871 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 1879 "src/parser.ml"
    )) = _v in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1884 "src/parser.ml"
    ) = 
# 60 "src/parser.mly"
    (TyUnit)
# 1888 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 23 "src/parser.mly"
      (string)
# 1895 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (tid : (
# 23 "src/parser.mly"
      (string)
# 1903 "src/parser.ml"
    )) = _v in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1908 "src/parser.ml"
    ) = 
# 54 "src/parser.mly"
    ( TyVar tid )
# 1912 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1924 "src/parser.ml"
    ) = 
# 50 "src/parser.mly"
    ( TyInt )
# 1928 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1940 "src/parser.ml"
    ) = 
# 52 "src/parser.mly"
    ( TyBool )
# 1944 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_atomicexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1951 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (e : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1961 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1968 "src/parser.ml"
        ) = 
# 102 "src/parser.mly"
        ( fst e, Proj(Left e) )
# 1972 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState102 | MenhirState99 | MenhirState21 | MenhirState26 | MenhirState93 | MenhirState87 | MenhirState89 | MenhirState82 | MenhirState84 | MenhirState77 | MenhirState79 | MenhirState30 | MenhirState73 | MenhirState31 | MenhirState68 | MenhirState70 | MenhirState65 | MenhirState39 | MenhirState60 | MenhirState62 | MenhirState54 | MenhirState58 | MenhirState56 | MenhirState50 | MenhirState52 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (s : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1981 "src/parser.ml"
        )) = _v in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1986 "src/parser.ml"
        ) = 
# 98 "src/parser.mly"
        ( s )
# 1990 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (a : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1999 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (f : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 2004 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 2009 "src/parser.ml"
        ) = 
# 100 "src/parser.mly"
        ( fst f, App(f,a) )
# 2013 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (e : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2022 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 2029 "src/parser.ml"
        ) = 
# 104 "src/parser.mly"
        ( fst e, Proj(Right e) )
# 2033 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_cmd_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Ast.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (_1 : (Ast.t))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 35 "src/parser.mly"
       (Ast.t)
# 2056 "src/parser.ml"
            ) = 
# 46 "src/parser.mly"
      ( _1 )
# 2060 "src/parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 35 "src/parser.mly"
       (Ast.t)
# 2067 "src/parser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.cmd Ast.loc))), _, (xs : (Ast.t))) = _menhir_stack in
        let _v : (Ast.t) = 
# 187 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 2083 "src/parser.ml"
         in
        _menhir_goto_list_cmd_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.BOOL ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | Tokens.INT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | Tokens.TYID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
            | Tokens.UNIT _v ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2134 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2142 "src/parser.ml"
    )) = _v in
    let _v : ((Utils.loc * Ast.var) * Ast.ty option) = 
# 136 "src/parser.mly"
        (id, None)
# 2147 "src/parser.ml"
     in
    _menhir_goto_param _menhir_env _menhir_stack _menhir_s _v

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 2154 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 2162 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2167 "src/parser.ml"
    ) = 
# 94 "src/parser.mly"
 ( _1, Unit )
# 2171 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 2178 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 2186 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2191 "src/parser.ml"
    ) = 
# 90 "src/parser.mly"
        ( _1, Bool true )
# 2195 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_run25 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 24 "src/parser.mly"
      (Utils.loc*int)
# 2225 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (n : (
# 24 "src/parser.mly"
      (Utils.loc*int)
# 2233 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2238 "src/parser.ml"
    ) = 
# 88 "src/parser.mly"
        ( fst n, Int(snd n) )
# 2242 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState81 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82)
        | Tokens.ID _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
        | Tokens.LEFTPAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState81
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81)
    | Tokens.REC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.EQUAL ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState29 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Tokens.FALSE _v ->
                    _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | Tokens.FST ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.FUN ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.ID _v ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | Tokens.IF ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.LEFTPAR ->
                    _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.LET ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.NUM _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | Tokens.SND ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState30
                | Tokens.TRUE _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | Tokens.UNIT _v ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
            | Tokens.ID _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
            | Tokens.LEFTPAR ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.FUN ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | Tokens.IF ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.LET ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState26
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | Tokens.FST ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | Tokens.FUN ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | Tokens.IF ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | Tokens.SND ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31

and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2431 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2439 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2444 "src/parser.ml"
    ) = 
# 82 "src/parser.mly"
       ( fst id, Var (snd id) )
# 2448 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState65
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | Tokens.LEFTPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.COLON ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Tokens.BOOL ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | Tokens.INT ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState36
                | Tokens.TYID _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
                | Tokens.UNIT _v ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | Tokens.ID _v ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | Tokens.LEFTPAR ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | Tokens.NUM _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | Tokens.TRUE _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | Tokens.UNIT _v ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 2572 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 2580 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2585 "src/parser.ml"
    ) = 
# 92 "src/parser.mly"
        ( _1, Bool false )
# 2589 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState70 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState26 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState12 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce33 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.t) = 
# 185 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 2761 "src/parser.ml"
     in
    _menhir_goto_list_cmd_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.ID _v ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState98 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | Tokens.FST ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.FUN ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.ID _v ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | Tokens.IF ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.LEFTPAR ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.LET ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.NUM _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | Tokens.SND ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState99
            | Tokens.TRUE _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | Tokens.UNIT _v ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
        | Tokens.ID _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
        | Tokens.LEFTPAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98)
    | Tokens.REC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ID _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.ID _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
            | Tokens.LEFTPAR ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and main : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 35 "src/parser.mly"
       (Ast.t)
# 2865 "src/parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.LET ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.EOF ->
        _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 219 "/home/manon/.opam/system/lib/menhir/standard.mly"
  


# 2892 "src/parser.ml"

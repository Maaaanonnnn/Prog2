
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
  | MenhirState105
  | MenhirState100
  | MenhirState97
  | MenhirState96
  | MenhirState91
  | MenhirState87
  | MenhirState85
  | MenhirState82
  | MenhirState80
  | MenhirState79
  | MenhirState77
  | MenhirState75
  | MenhirState71
  | MenhirState68
  | MenhirState66
  | MenhirState63
  | MenhirState60
  | MenhirState58
  | MenhirState56
  | MenhirState54
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState43
  | MenhirState38
  | MenhirState37
  | MenhirState34
  | MenhirState29
  | MenhirState28
  | MenhirState27
  | MenhirState24
  | MenhirState22
  | MenhirState20
  | MenhirState17
  | MenhirState13
  | MenhirState11
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
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState105
    | Tokens.EOF ->
        _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack) MenhirState105
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105

and _menhir_goto_letexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 97 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState28 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState71
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 148 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 152 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 156 "src/parser.ml"
        ))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 165 "src/parser.ml"
        ) = 
# 125 "src/parser.mly"
        ( fst id, LetIn(snd id, (fst t, Fix(fst id, Lam(snd id, None, t))), u) )
# 169 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState75 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState77
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
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
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 218 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 222 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 226 "src/parser.ml"
        ))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 235 "src/parser.ml"
        ) = 
# 127 "src/parser.mly"
        ( fst id, LetIn(snd id, (fst t, Fix(mk_lam ((id, None)::ps) t)), u) )
# 239 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState80 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 288 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 292 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 296 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 304 "src/parser.ml"
        ) = 
# 121 "src/parser.mly"
        ( fst id, LetIn(snd id, t,u)  )
# 308 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState85 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState87
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
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
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 357 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 361 "src/parser.ml"
        ))), _, (u : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 365 "src/parser.ml"
        ))) = _menhir_stack in
        let _6 = () in
        let _4 = () in
        let _1 = () in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 373 "src/parser.ml"
        ) = 
# 123 "src/parser.mly"
        ( fst id, LetIn(snd id, mk_lam ps t,u)  )
# 377 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState24 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 421 "src/parser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 428 "src/parser.ml"
            ) = 
# 82 "src/parser.mly"
       ( e )
# 432 "src/parser.ml"
             in
            _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState91 ->
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
# 453 "src/parser.ml"
            ))), _, (er : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 457 "src/parser.ml"
            ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 465 "src/parser.ml"
            ) = 
# 84 "src/parser.mly"
      ( fst el, Pair(el,er) )
# 469 "src/parser.ml"
             in
            _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 484 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 488 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 142 "src/parser.mly"
        ( fst id, LetRec(snd id, None, mk_lam ps t) )
# 496 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 505 "src/parser.ml"
        ))), _), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 509 "src/parser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 138 "src/parser.mly"
        ( fst id, Let(snd id, None, t) )
# 516 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 525 "src/parser.ml"
        ))), _, (ps : (((Utils.loc * Ast.var) * Ast.ty option) list))), _, (t : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 529 "src/parser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _1 = () in
        let _v : (Ast.cmd Ast.loc) = 
# 140 "src/parser.mly"
        ( fst id, Let(snd id, None, mk_lam ps t) )
# 536 "src/parser.ml"
         in
        _menhir_goto_cmd _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_funexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 545 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 556 "src/parser.ml"
        ))), _, (ty : (
# 42 "src/parser.mly"
      (ty)
# 560 "src/parser.ml"
        ))), _, (t : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 564 "src/parser.ml"
        ))) = _menhir_stack in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 574 "src/parser.ml"
        ) = 
# 115 "src/parser.mly"
        ( fst id, Lam(snd id, (Some ty), t) )
# 578 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 587 "src/parser.ml"
        ))), _, (t : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 591 "src/parser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 598 "src/parser.ml"
        ) = 
# 113 "src/parser.mly"
        ( fst id, Lam(snd id, None, t) )
# 602 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState29 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState66
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState66
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState66
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState66
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState66
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState66 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState68
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
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
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (cond : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 687 "src/parser.ml"
        ))), _, (l : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 691 "src/parser.ml"
        ))), _, (r : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 695 "src/parser.ml"
        ))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 703 "src/parser.ml"
        ) = 
# 111 "src/parser.mly"
        ( fst cond, Ite(cond,l,r) )
# 707 "src/parser.ml"
         in
        _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState100 | MenhirState97 | MenhirState20 | MenhirState24 | MenhirState91 | MenhirState85 | MenhirState87 | MenhirState80 | MenhirState82 | MenhirState75 | MenhirState77 | MenhirState28 | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (s : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 716 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 41 "src/parser.mly"
      (Utils.loc * expr)
# 721 "src/parser.ml"
        ) = 
# 119 "src/parser.mly"
        ( s )
# 725 "src/parser.ml"
         in
        _menhir_goto_letexpr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run43 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 734 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState43
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_run48 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 762 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48

and _menhir_run52 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 790 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52

and _menhir_run54 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 818 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState54
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54

and _menhir_run56 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 846 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState56
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56

and _menhir_run50 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 874 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_run60 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 902 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState60
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60

and _menhir_run11 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 42 "src/parser.mly"
      (ty)
# 930 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.BOOL ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | Tokens.INT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState11
    | Tokens.TYID _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11

and _menhir_run13 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 42 "src/parser.mly"
      (ty)
# 950 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.BOOL ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | Tokens.INT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState13
    | Tokens.TYID _v ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13

and _menhir_goto_binopexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 970 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState100 | MenhirState97 | MenhirState20 | MenhirState24 | MenhirState91 | MenhirState85 | MenhirState87 | MenhirState80 | MenhirState82 | MenhirState75 | MenhirState77 | MenhirState28 | MenhirState71 | MenhirState29 | MenhirState66 | MenhirState68 | MenhirState63 | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
        | Tokens.GT ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.OR ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.IN | Tokens.LET | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (s : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1022 "src/parser.ml"
            ))) = _menhir_stack in
            let _v : (
# 40 "src/parser.mly"
      (Utils.loc * expr)
# 1027 "src/parser.ml"
            ) = 
# 109 "src/parser.mly"
        ( s )
# 1031 "src/parser.ml"
             in
            _menhir_goto_funexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1046 "src/parser.ml"
        ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1050 "src/parser.ml"
        ))) = _menhir_stack in
        let _10 = () in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1056 "src/parser.ml"
        ) = let b =
          let _1 = _10 in
          
# 66 "src/parser.mly"
    ( Times )
# 1062 "src/parser.ml"
          
        in
        
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1068 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1085 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1089 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1095 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 62 "src/parser.mly"
    ( Plus )
# 1101 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1107 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1122 "src/parser.ml"
        ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1126 "src/parser.ml"
        ))) = _menhir_stack in
        let _10 = () in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1132 "src/parser.ml"
        ) = let b =
          let _1 = _10 in
          
# 68 "src/parser.mly"
    ( Div )
# 1138 "src/parser.ml"
          
        in
        
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1144 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1167 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1171 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1177 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 72 "src/parser.mly"
    ( Or )
# 1183 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1189 "src/parser.ml"
             in
            _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1212 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1216 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1222 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 64 "src/parser.mly"
    ( Minus )
# 1228 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1234 "src/parser.ml"
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
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1261 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1265 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1271 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 76 "src/parser.mly"
    ( Gt )
# 1277 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1283 "src/parser.ml"
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
        | Tokens.AND ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.OR ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1316 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1320 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1326 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 74 "src/parser.mly"
    ( Eq )
# 1332 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1338 "src/parser.ml"
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
        | Tokens.DIV ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.MINUS ->
            _menhir_run54 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.TIMES ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AND | Tokens.COMMA | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.IN | Tokens.LET | Tokens.OR | Tokens.RIGHTPAR | Tokens.THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (el : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1367 "src/parser.ml"
            ))), _, (er : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1371 "src/parser.ml"
            ))) = _menhir_stack in
            let _10 = () in
            let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1377 "src/parser.ml"
            ) = let b =
              let _1 = _10 in
              
# 70 "src/parser.mly"
    ( And )
# 1383 "src/parser.ml"
              
            in
            
# 106 "src/parser.mly"
        ( fst el, Binop(b,el,er) )
# 1389 "src/parser.ml"
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
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : ((Utils.loc * Ast.var) * Ast.ty option))), _, (xs : (((Utils.loc * Ast.var) * Ast.ty option) list))) = _menhir_stack in
        let _v : (((Utils.loc * Ast.var) * Ast.ty option) list) = 
# 197 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 1412 "src/parser.ml"
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState27 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState75
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState79 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState85
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState96 ->
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState100
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100)
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
# 1581 "src/parser.ml"
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
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 1600 "src/parser.ml"
            ))), _, (ty : (
# 42 "src/parser.mly"
      (ty)
# 1604 "src/parser.ml"
            ))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : ((Utils.loc * Ast.var) * Ast.ty option) = 
# 134 "src/parser.mly"
        (id, Some ty)
# 1612 "src/parser.ml"
             in
            _menhir_goto_param _menhir_env _menhir_stack _menhir_s _v
        | Tokens.TIMES ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR | Tokens.TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (tl : (
# 42 "src/parser.mly"
      (ty)
# 1635 "src/parser.ml"
            ))), _, (tr : (
# 42 "src/parser.mly"
      (ty)
# 1639 "src/parser.ml"
            ))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 42 "src/parser.mly"
      (ty)
# 1645 "src/parser.ml"
            ) = 
# 58 "src/parser.mly"
    ( TyTimes(tl,tr) )
# 1649 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RIGHTPAR | Tokens.TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (tl : (
# 42 "src/parser.mly"
      (ty)
# 1670 "src/parser.ml"
            ))), _, (tr : (
# 42 "src/parser.mly"
      (ty)
# 1674 "src/parser.ml"
            ))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 42 "src/parser.mly"
      (ty)
# 1680 "src/parser.ml"
            ) = 
# 56 "src/parser.mly"
    ( TyArrow(tl,tr) )
# 1684 "src/parser.ml"
             in
            _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | Tokens.ARROW ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack)
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
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
                | Tokens.FST ->
                    _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState37
                | Tokens.FUN ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState37
                | Tokens.ID _v ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
                | Tokens.IF ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState37
                | Tokens.LEFTPAR ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState37
                | Tokens.NUM _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
                | Tokens.SND ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState37
                | Tokens.TRUE _v ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | Tokens.TIMES ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack)
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
# 1752 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | Tokens.AND | Tokens.COMMA | Tokens.DIV | Tokens.ELSE | Tokens.EOF | Tokens.EQUAL | Tokens.GT | Tokens.IN | Tokens.LET | Tokens.MINUS | Tokens.OR | Tokens.PLUS | Tokens.RIGHTPAR | Tokens.THEN | Tokens.TIMES ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (s : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1775 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 38 "src/parser.mly"
      (Utils.loc * expr)
# 1780 "src/parser.ml"
        ) = 
# 104 "src/parser.mly"
        ( s )
# 1784 "src/parser.ml"
         in
        _menhir_goto_binopexpr _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46

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
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | Tokens.LEFTPAR ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | Tokens.EQUAL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : ((Utils.loc * Ast.var) * Ast.ty option))) = _menhir_stack in
        let _v : (((Utils.loc * Ast.var) * Ast.ty option) list) = 
# 195 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( [ x ] )
# 1814 "src/parser.ml"
         in
        _menhir_goto_nonempty_list_param_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 23 "src/parser.mly"
      (string)
# 1825 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (tid : (
# 23 "src/parser.mly"
      (string)
# 1833 "src/parser.ml"
    )) = _v in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1838 "src/parser.ml"
    ) = 
# 54 "src/parser.mly"
    ( TyVar tid )
# 1842 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (
# 42 "src/parser.mly"
      (ty)
# 1854 "src/parser.ml"
    ) = 
# 50 "src/parser.mly"
    ( TyInt )
# 1858 "src/parser.ml"
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
# 1870 "src/parser.ml"
    ) = 
# 52 "src/parser.mly"
    ( TyBool )
# 1874 "src/parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_atomicexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1881 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (e : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1891 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1898 "src/parser.ml"
        ) = 
# 98 "src/parser.mly"
        ( fst e, Proj(Left e) )
# 1902 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState100 | MenhirState97 | MenhirState20 | MenhirState24 | MenhirState91 | MenhirState85 | MenhirState87 | MenhirState80 | MenhirState82 | MenhirState75 | MenhirState77 | MenhirState28 | MenhirState71 | MenhirState29 | MenhirState66 | MenhirState68 | MenhirState63 | MenhirState37 | MenhirState58 | MenhirState60 | MenhirState52 | MenhirState56 | MenhirState54 | MenhirState48 | MenhirState50 | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (s : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1911 "src/parser.ml"
        )) = _v in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1916 "src/parser.ml"
        ) = 
# 94 "src/parser.mly"
        ( s )
# 1920 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (a : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1929 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s, (f : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1934 "src/parser.ml"
        ))) = _menhir_stack in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1939 "src/parser.ml"
        ) = 
# 96 "src/parser.mly"
        ( fst f, App(f,a) )
# 1943 "src/parser.ml"
         in
        _menhir_goto_appexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (e : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 1952 "src/parser.ml"
        )) = _v in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : (
# 39 "src/parser.mly"
      (Utils.loc * expr)
# 1959 "src/parser.ml"
        ) = 
# 100 "src/parser.mly"
        ( fst e, Proj(Right e) )
# 1963 "src/parser.ml"
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
# 1986 "src/parser.ml"
            ) = 
# 46 "src/parser.mly"
      ( _1 )
# 1990 "src/parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 35 "src/parser.mly"
       (Ast.t)
# 1997 "src/parser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Ast.cmd Ast.loc))), _, (xs : (Ast.t))) = _menhir_stack in
        let _v : (Ast.t) = 
# 187 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( x :: xs )
# 2013 "src/parser.ml"
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
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | Tokens.INT ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6
            | Tokens.TYID _v ->
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

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2062 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2070 "src/parser.ml"
    )) = _v in
    let _v : ((Utils.loc * Ast.var) * Ast.ty option) = 
# 132 "src/parser.mly"
        (id, None)
# 2075 "src/parser.ml"
     in
    _menhir_goto_param _menhir_env _menhir_stack _menhir_s _v

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 2082 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 2090 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2095 "src/parser.ml"
    ) = 
# 88 "src/parser.mly"
        ( _1, Bool true )
# 2099 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 24 "src/parser.mly"
      (Utils.loc*int)
# 2127 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (n : (
# 24 "src/parser.mly"
      (Utils.loc*int)
# 2135 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2140 "src/parser.ml"
    ) = 
# 86 "src/parser.mly"
        ( fst n, Int(snd n) )
# 2144 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run25 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
            let _menhir_s = MenhirState79 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState80
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
        | Tokens.ID _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | Tokens.LEFTPAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
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
                let _menhir_s = MenhirState27 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | Tokens.FALSE _v ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
                | Tokens.FST ->
                    _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.FUN ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.ID _v ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
                | Tokens.IF ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.LEFTPAR ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.LET ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.NUM _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
                | Tokens.SND ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState28
                | Tokens.TRUE _v ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28)
            | Tokens.ID _v ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
            | Tokens.LEFTPAR ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState27
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27)
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

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.FUN ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.IF ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.LET ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | Tokens.FST ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | Tokens.FUN ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | Tokens.IF ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | Tokens.SND ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState29
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2325 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (id : (
# 22 "src/parser.mly"
      (Utils.loc*string)
# 2333 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2338 "src/parser.ml"
    ) = 
# 80 "src/parser.mly"
       ( fst id, Var (snd id) )
# 2342 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState63
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
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
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState34
                | Tokens.INT ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState34
                | Tokens.TYID _v ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34)
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

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | Tokens.FALSE _v ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | Tokens.ID _v ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | Tokens.LEFTPAR ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | Tokens.NUM _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | Tokens.TRUE _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 25 "src/parser.mly"
      (Utils.loc)
# 2460 "src/parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (
# 25 "src/parser.mly"
      (Utils.loc)
# 2468 "src/parser.ml"
    )) = _v in
    let _v : (
# 37 "src/parser.mly"
      (Utils.loc * expr)
# 2473 "src/parser.ml"
    ) = 
# 90 "src/parser.mly"
        ( _1, Bool false )
# 2477 "src/parser.ml"
     in
    _menhir_goto_atomicexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState85 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState68 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
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
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState37 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState28 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
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

and _menhir_reduce32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Ast.t) = 
# 185 "/home/manon/.opam/system/lib/menhir/standard.mly"
    ( [] )
# 2649 "src/parser.ml"
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
            let _menhir_s = MenhirState96 in
            let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | Tokens.FALSE _v ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | Tokens.FST ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.FUN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.ID _v ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | Tokens.IF ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.LEFTPAR ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.LET ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.NUM _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | Tokens.SND ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState97
            | Tokens.TRUE _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97)
        | Tokens.ID _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
        | Tokens.LEFTPAR ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState96
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
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
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
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
# 2751 "src/parser.ml"
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
        _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 219 "/home/manon/.opam/system/lib/menhir/standard.mly"
  


# 2778 "src/parser.ml"

Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(*idiomatic way to take a string as input? loop? *)
Definition check_password :=
  func! (password, passwordlen)
    {
      io! attempt = MMIOREAD($0)

    }.

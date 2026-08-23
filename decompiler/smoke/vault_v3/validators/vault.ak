//! Smoke fixture for the decompiler test-suite.
//!
//! Authored for this repository: a small vault validator that exercises
//! constructor dispatch, record field access, recursion over a list and a
//! few ByteArray builtins, so the decompiler pipeline has something with
//! shape to chew on. It is deliberately not derived from any deployed
//! contract.

use aiken/builtin

pub type Action {
  Transfer { amount: Int, recipient: ByteArray }
  Extend { extra: Int, witnesses: List<ByteArray> }
  Close
}

pub type Vault {
  owner: ByteArray,
  total: Int,
  epoch: Int,
}

fn total_of(amounts: List<Int>) -> Int {
  when amounts is {
    [] -> 0
    [head, ..rest] -> head + total_of(rest)
  }
}

fn join_all(chunks: List<ByteArray>) -> ByteArray {
  when chunks is {
    [] -> #""
    [head, ..rest] -> builtin.append_bytearray(head, join_all(rest))
  }
}

fn count_of(chunks: List<ByteArray>) -> Int {
  when chunks is {
    [] -> 0
    [_head, ..rest] -> 1 + count_of(rest)
  }
}

fn label_of(entry: Vault) -> ByteArray {
  builtin.append_bytearray(entry.owner, #"5641554c54")
}

validator vault {
  spend(datum: Option<Vault>, redeemer: Action, _utxo: Data, _self: Data) {
    when datum is {
      Some(state) -> {
        let label: ByteArray = label_of(state)
        let budget: Int = state.total - state.epoch
        when redeemer is {
          Transfer { amount, recipient } -> {
            let fee: Int = amount / 10
            amount > 0 && fee <= budget && label != recipient
          }
          Extend { extra, witnesses } -> {
            let joined: ByteArray = join_all(witnesses)
            let seats: Int = count_of(witnesses)
            seats > 0 && extra > 0 && builtin.slice_bytearray(0, 4, joined) != label
          }
          Close -> total_of([state.total, state.epoch, budget]) == 0
        }
      }
      None -> False
    }
  }

  mint(redeemer: Action, _policy: ByteArray, _self: Data) {
    when redeemer is {
      Transfer { amount, recipient } -> amount > 0 && recipient != #""
      Extend { extra, witnesses } -> extra > 0 && count_of(witnesses) > 1
      Close -> False
    }
  }

  else(_) {
    fail
  }
}

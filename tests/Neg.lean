import E708C.Defs
namespace E708F
def mOKH4 (H m : Nat) : Bool :=
  let cA := mkC H m
  let pA := mkPM cA m
  tabOK H m (fun a => cA.getD a 100) (fun d => pA.getD d 100) &&
  enum4 H m (fun a => cA.getD a 100) (fun d => pA.getD d 100) (fullOK H m)
-- negative tests: the checker must reject wrong certificates and too-small budgets
#eval checkTup 8 462 [210,330,420,462] [([],[1]),([],[330]),([],[105,4]),([],[154,3])]  -- false (210 ∤ 1)
#eval checkTup 8 462 [210,330,420,462] [([],[210]),([],[330]),([],[105,4]),([],[154,3])] -- true
#eval checkTup 5 462 [210,330,420,462] [([],[210]),([],[330]),([],[105,4]),([],[154,3])] -- false (6 > 5)
#eval checkTup 8 462 [210,330,420,462] [([(2,1)],[105]),([],[330]),([],[105,4]),([],[154,3])] -- true
#eval checkTup 8 462 [210,330,420,462] [([(4,1)],[105]),([],[330]),([],[105,4]),([],[154,3])] -- false (4 not prime)
#eval (List.range' 9 120).all (mOKH4 4)   -- false: g(4) ≥ 5
#eval (List.range' 9 120).filter (fun m => !(mOKH4 4 m)) |>.take 5
end E708F

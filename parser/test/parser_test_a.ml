open TestFramework

let _ =
  describe "my first test suite"
    (fun { test }  ->
       test "1 + 1 should equal 2"
         (fun { expect }  -> (expect.int (1 + 1)).toBe 3))
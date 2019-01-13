let f n = "F"^(string_of_int n)^" f x1 x0 = F"^(string_of_int (n+1))^" (F"^(string_of_int (n+1))^" f) x1 x0.";;
let gen n fp =
  for i=0 to n do
    output_string fp ((f i)^"\n");flush fp
done;;
let main n fname =
 let fp = open_out fname in
output_string fp "%BEGING\nS = F0 G2 G1 G0.\n";
gen n fp;
output_string fp ("F"^(string_of_int (n+1))^" f x1 x0 = G3 f x1 x0.\n");
output_string fp "G3 f z x0 = f (f z) x0.\nG2 f z = f (f z).\nG1 z = a z.\nG0 = c.\n%ENDG\n%BEGINA\nq0 a -> q1.\nq1 a -> q0.\nq0 c -> .\n%ENDA\n";
close_out fp



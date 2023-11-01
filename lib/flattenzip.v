From mathcomp Require Import seq.

Module flattenzip.

Definition flatten1_2zipped [s p q: Type] (nested: list (s * (p * q))): (list (s * p * q)):=
	map (fun '(a, (b, c)) => (a, b, c)) nested.

Definition flatten1_3zipped [s p q r: Type] (nested: list (s * (p * q * r))): (list (s * p * q * r)):=
	map (fun '(a, (b, c, d)) => (a, b, c, d)) nested.

Definition flatten1_4zipped [s p q r w: Type] (nested: list (s * (p * q * r * w))): (list (s * p * q * r * w)):=
	map (fun '(a, (b, c, d, e)) => (a, b, c, d, e)) nested.

Definition flatten2_2zipped [s t p q: Type] (nested: list (s * t * (p * q))): (list (s * t * p * q)):=
	map (fun '(a, b, (c, d)) => (a, b, c, d)) nested.

Definition flatzip1_2 [s p q: Type] (sqa: seq s) (sqb: seq (p * q)): (seq (s * p * q)):=
	flatten1_2zipped (zip sqa sqb).

Definition flatzip1_3 [s p q r: Type] (sqa: seq s) (sqb: seq (p * q * r)): (seq (s * p * q * r)):=
	flatten1_3zipped (zip sqa sqb).

Definition flatzip1_4 [s p q r w: Type] (sqa: seq s) (sqb: seq (p * q * r * w)): (seq (s * p * q * r * w)):=
	flatten1_4zipped (zip sqa sqb).

Definition flatzip2_2 [s t p q: Type] (sqa: seq (s * t)) (sqb: seq (p * q)): (seq (s * t * p * q)):=
	flatten2_2zipped (zip sqa sqb).

End flattenzip.

Export flattenzip.
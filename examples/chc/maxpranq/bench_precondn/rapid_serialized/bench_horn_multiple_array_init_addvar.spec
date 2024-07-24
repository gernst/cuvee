func main()
{
	Int[] a;
	const Int alength;
	Int i = 1;
        
	while(i < alength)
	{
            const Int j;
            if (i <= j) {
	           a[i] = j;
	           i = i + 1;
	       } else {
	           skip;
	       }
	}
	i = 0;
	while (i < alength)
	{
	  a[i] = a[i] + i;
	  i = i + 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (< 0 pos)
	  (< pos alength)
	  (<= alength (i main_end))
         )
       (<=  (* 2 pos) (a main_end pos))
      )
   )
)

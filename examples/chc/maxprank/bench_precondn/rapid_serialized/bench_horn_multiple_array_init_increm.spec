func main()
{
	Int[] a;
	const Int alength;
	Int i = 1;
	
	while(i < alength)
                     {
	    const Int j;
            if (0 <= j) {
                   a[i] = j;
                   i = i + 1;
               } else {
                   skip;
               }
        }

	i = 0;
	while (i < alength)
	{
	  a[i] = a[i] + 1;
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
       (<= 1 (a main_end pos))
      )
   )
)

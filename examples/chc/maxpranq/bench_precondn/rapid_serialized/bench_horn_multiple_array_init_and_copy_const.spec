func main()
{
	Int[] a;
	Int[] b;
	const Int alength;
	Int i = 1;
	
	while(i < alength)
             {
	    const Int j;
            if (1 <= j) {
                   a[i] = j;
                   i = i + 1;
               } else {
                   skip;
               }
        }
	i = 0;
	while (i < alength)
	{
	  b[i] = a[i];
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
       (<= 1 (b main_end pos))
      )
   )
)

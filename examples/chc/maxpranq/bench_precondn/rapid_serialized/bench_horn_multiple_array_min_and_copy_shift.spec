func main()
{
	Int[] a;
	Int[] b;
	const Int alength;

	Int i = 1;
	const Int j;
        
	while(i < alength)
	     {
                 const Int k;
	  if (j <= k) {
	         a[i] = k;
                 i = i + 1;
	  } else {
	    skip;
	  }
	}
	i = 0;
	while(i < alength)
	{
	  b[i] = a[i] - j;
	  i = i + 1;
	}
	
	
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
	  (< pos alength)
	  (<= alength (i main_end))
         )
       (>= (b main_end pos) 0)
      )
   )
)

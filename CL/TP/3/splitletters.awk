	#Laurent BESACIER
	#usage : cat *.txt | awk -f clean.awk

	{
	N=split($0,tab,"");
	for (i=1; i<=N; i++)
		{
		printf tab[i]" "
		}
	printf "\n"
	}





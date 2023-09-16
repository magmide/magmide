type Day;
	| Monday
	| Tuesday
	| Wednesday
	| Thursday
	| Friday
	| Saturday
	| Sunday

proc next_weekday(d: Day): Day;
	match d;
		Day.Monday => Day.Tuesday
		Day.Tuesday => Day.Wednesday
		Day.Wednesday => Day.Thursday
		Day.Thursday => Day.Friday
		_ => Day.Monday

proc same_day(d: Day): Day;
	d

prop Eq(@T: type): [T, T];
	(t: T): [t, t]

thm example_next_weekday: Eq[next_weekday(Day.Saturday), Day.Monday];
	Eq(Day.Monday)

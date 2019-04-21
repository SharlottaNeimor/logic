def Logger(F,text):
	with open('./out.txt','a') as f: f.write(F+'		NOTE: '+text+'\n')
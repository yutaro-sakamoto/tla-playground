# run TLA+ tools
all: example.tla example.cfg tla2tools.jar
	java -cp tla2tools.jar pcal.trans example.tla
	java -jar tla2tools.jar -config example.cfg example.tla

# generate a configuration file
example.cfg: tla2tools.jar example.tla
	java -cp tla2tools.jar pcal.trans example.tla

# download tla2tools.jar
tla2tools.jar:
	curl -L -o tla2tools.jar  https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

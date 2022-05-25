//Projeto Métodos Formais - Sistema Operacional
//Alice Ziemer, Danilo Rocha e Felipe Ribeiro

one sig SistemaOperacional {
	pastaRoot: one Root,
	categorias: set CategoriaUsuario
}

abstract sig Objeto {
	parent : lone Diretorio
}

sig Arquivo extends Objeto {}

sig Diretorio extends Objeto {
	conteudo : set Objeto
}

one sig Root extends Diretorio {} { no parent }

sig Usuario {}

abstract sig Permissao {}

one sig Leitura, LeituraEscrita, Dono extends Permissao {}

abstract sig CategoriaUsuario {
	usuarios : set Usuario
}

one sig ParaTodos, UsuariosExternos, UsuariosDestePC extends CategoriaUsuario {}
 
fact "Diretorio é parent de seus conteúdos" { 
	all d: Diretorio, c: d.conteudo | c.parent = d
}

fact "Nao é parent de si mesmo" { 
	all o: Objeto | o->o not in parent and o->o not in conteudo
}

fact "Objetos Conectados" { 
	Objeto in Root.*conteudo
}

fact "Todas as Categorias pertencem ao Sistema" { 
	all c: CategoriaUsuario, s: SistemaOperacional | c in s.categorias
}

//fact "Categorias têm relacionamento com todas as Permissões" {}

assert arquivoIsConteudo { //garantindo que todos os arquivos sejam conteúdo de alguma pasta
	all a: Arquivo | a in univ.conteudo
}

check arquivoIsConteudo for 5

pred usuarioUnico [c: CategoriaUsuario] { 
	all u1, u2: Usuario | u1 in c.usuarios && u2 in c.usuarios => u1 != u2
}

run usuarioUnico {} for 5

//run exemplo {} for 3 but 2 Objeto, exactly 3 Arquivo

//run exemplo {}

//run exemplo {  some Arquivo
// some Diretorio - Root
//  some Usuario
//} for 7

import * as vscode from 'vscode'
import * as vsc from 'vscode-languageclient/node'
	

let client: vsc.LanguageClient;

export function activate(context: vscode.ExtensionContext) {

	const cfg= vscode.workspace.getConfiguration("cryptol") 
	let serverExe = cfg["language-server-path"]
	console.log(serverExe)

	let srvCfg = { command: serverExe, transport: vsc.TransportKind.stdio }
    let srvOpt: vsc.ServerOptions =	{ run: srvCfg, debug: srvCfg }
    let cltOpt: vsc.LanguageClientOptions = {
	  documentSelector: [{ scheme: 'file', language: 'cryptol' }]
	};

	client = new vsc.LanguageClient("cryptol", srvOpt, cltOpt)
	client.onReady().then(() => {

	});

	client.start();

}


export function deactivate() {
	if (!client) { return }
	client.stop()
}

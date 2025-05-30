import * as vscode from 'vscode'
import * as vsc from 'vscode-languageclient/node'
	

let client: vsc.LanguageClient;


async function callServer(command: string, args: any[]): Promise<void> {
	const params = { command: command, arguments: args }
	return new Promise<void>(
	  () => client.sendRequest(vsc.ExecuteCommandRequest.type, params))
}


export function activate(context: vscode.ExtensionContext) {

	function getCurrentDoc(): string | null {
	  const editor = vscode.window.activeTextEditor
	  if (editor === undefined) { return null }
	  return editor.document.uri.toString()
	}

	function callWithCurrentDoc(cmd: string) {
	  const uri = getCurrentDoc()
	  if (uri === null) { return }
	  callServer(cmd,[uri])
	}

	const cmdReload =
	  vscode.commands.registerCommand('cryptol.reload', () =>
		callWithCurrentDoc("reload")
	)

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

	context.subscriptions.push(cmdReload)
	client.start();

}


export function deactivate() {
	if (!client) { return }
	client.stop()
}

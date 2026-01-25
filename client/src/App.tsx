import { useCallback, useEffect, useRef, useState, JSX } from 'react'
import * as React from 'react'
import Split from 'react-split'
import * as monaco from 'monaco-editor'
import CodeMirror, { EditorView } from '@uiw/react-codemirror'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import LZString from 'lz-string'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faCode } from '@fortawesome/free-solid-svg-icons'
import * as path from 'path'

// Local imports
import LeanLogo from './assets/logo.svg'
import defaultSettings, { IPreferencesContext, lightThemes, preferenceParams } from './config/settings'
import { Menu } from './Navigation'
import { PreferencesContext } from './Popups/Settings'
import { Entries } from './utils/Entries'
import { save } from './utils/SaveToFile'
import { fixedEncodeURIComponent, formatArgs, lookupUrl, parseArgs } from './utils/UrlParsing'
import { useWindowDimensions } from './utils/WindowWidth'
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { Goals } from './infoview';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { RpcSessionManager } from './RpcSessionManager';

type LevelDefinition = {
  name: string;
  initial: BlocklyState;
};

const levelDefinitions: LevelDefinition[] = [
  {
    name: "Limit Example",
    initial: { "blocks": { "languageVersion": 0, "blocks": [{ "type": "lemma", "id": "3yAUmdNL2=WYh]Gxi)]X", "x": 13, "y": 22, "fields": { "THEOREM_NAME": "away", "THEOREM_DECLARATION": "(y : ℝ) (hy : y ≠ 1) : (y^2 - 1) / (y - 1) = y + 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_other", "id": "k}|H70s[,ot=/1U@K_,;", "fields": { "PROP_NAME": "grind" } } } } }, { "type": "lemma", "id": "DemnP%+kbpZdIIe~0(3W", "x": 308, "y": 35, "fields": { "THEOREM_NAME": "fun_limit_fact", "THEOREM_DECLARATION": ": FunLimAt (fun x => (x^2 - 1) / (x - 1)) 2 1" }, "inputs": { "LEMMA_PROOF": { "block": { "type": "tactic_unfold", "id": "4jk;hHJ|_aSp.)2PU`Gc", "inputs": { "ARG": { "block": { "type": "prop", "id": "Mojm{fSn$rJvFC81z{h(", "fields": { "PROP_NAME": "FunLimAt" } } } }, "next": { "block": { "type": "tactic_intro", "id": "^=/m!cJjN6xgQ.RpEN]y", "inputs": { "ARG": { "block": { "type": "prop", "id": "Y(gRn,NBi~2+wLabs!@A", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_intro", "id": "MK{[.T(RH!$~`CKvXmL1", "inputs": { "ARG": { "block": { "type": "prop", "id": "mgxS^6SsXB-}9:6^cQ?!", "fields": { "PROP_NAME": "hε" } } } }, "next": { "block": { "type": "tactic_use", "id": "QPSB(Ek%b~pXS8}W4?4/", "inputs": { "ARG": { "block": { "type": "prop", "id": "^XKO;%FbY-Cl)sU%fNl;", "fields": { "PROP_NAME": "ε" } } } }, "next": { "block": { "type": "tactic_constructor", "id": "C=S-)mM.)`C``sWq!YlT", "inputs": { "BODY1": { "block": { "type": "tactic_other", "id": "m.6n,uHODs!Ns?ycFg`M", "fields": { "PROP_NAME": "linarith" } } }, "BODY2": { "block": { "type": "tactic_intro", "id": "4Nh1ti#nH_#d-A3V$e|_", "inputs": { "ARG": { "block": { "type": "prop", "id": ":un028QY,n#E7%_%,]4[", "fields": { "PROP_NAME": "y" } } } }, "next": { "block": { "type": "tactic_intro", "id": "fxEi-:)M^j3ee76?Z9l+", "inputs": { "ARG": { "block": { "type": "prop", "id": "U:5}c2^h7F]d8+hh(q}8", "fields": { "PROP_NAME": "hy" } } } }, "next": { "block": { "type": "tactic_intro", "id": "]@#*lMzE^dbkiR]{PhGo", "inputs": { "ARG": { "block": { "type": "prop", "id": "*ww_S)5(YZG^Uc84eUlv", "fields": { "PROP_NAME": "hy2" } } } }, "next": { "block": { "type": "tactic_other", "id": "3#gT|oNu-}[}3uB_a.2U", "fields": { "PROP_NAME": "simp" }, "next": { "block": { "type": "tactic_rw", "id": "f5piLnWwQvlx,Ki5WTp4", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "prop", "id": "G.]vQSXK]?]G9T#)g+sJ", "fields": { "PROP_NAME": "away y hy" } } } }, "next": { "block": { "type": "tactic_rw", "id": "W|.ZlRq5@bi.2CML=mPB", "fields": { "DIRECTION_TYPE": "RIGHT" }, "inputs": { "REWRITE_SOURCE": { "block": { "type": "tactic_show", "id": "3{s96}qox|({ahT!Azz)", "inputs": { "GOAL": { "block": { "type": "prop", "id": "!bFf)T7:^+.{UW4*Cf*}", "fields": { "PROP_NAME": "y + 1 - 2 = y - 1" } } }, "PROOF": { "block": { "type": "tactic_other", "id": "fqI`{J4OU;d~Kx3hWy%e", "fields": { "PROP_NAME": "grind" } } } } } } }, "next": { "block": { "type": "tactic_exact", "id": "HSp12q.iHmw-1[hrEQB@", "inputs": { "ARG": { "block": { "type": "prop", "id": ",)45@UUo`{kGa5cYgWS8", "fields": { "PROP_NAME": "hy2" } } } } } } } } } } } } } } } } } } } } } } } } } } } } } } }] } }
  },
  {
    name: "Simple Add",
    initial: {
      "blocks": {
        "languageVersion": 0,
        "blocks": [{
          "type": "lemma",
          "id": "example2-lemma",
          "x": 20,
          "y": 20,
          "fields": {
            "THEOREM_NAME": "simple_add",
            "THEOREM_DECLARATION": ": 1 + 1 = 2"
          },
          "inputs": {
            "LEMMA_PROOF": {
              "block": {
                "type": "tactic_other",
                "id": "example2-tactic",
                "fields": { "PROP_NAME": "rfl" }
              }
            }
          }
        }]
      }
    }
  },
  {
    name: "Add Comm",
    initial: {
      "blocks": {
        "languageVersion": 0,
        "blocks": [{
          "type": "lemma",
          "id": "example3-lemma",
          "x": 20,
          "y": 20,
          "fields": {
            "THEOREM_NAME": "add_comm_example",
            "THEOREM_DECLARATION": "(a b : ℕ) : a + b = b + a"
          },
          "inputs": {
            "LEMMA_PROOF": {
              "block": {
                "type": "tactic_intro",
                "id": "example3-intro1",
                "inputs": {
                  "ARG": {
                    "block": {
                      "type": "prop",
                      "id": "example3-prop1",
                      "fields": { "PROP_NAME": "a" }
                    }
                  }
                },
                "next": {
                  "block": {
                    "type": "tactic_intro",
                    "id": "example3-intro2",
                    "inputs": {
                      "ARG": {
                        "block": {
                          "type": "prop",
                          "id": "example3-prop2",
                          "fields": { "PROP_NAME": "b" }
                        }
                      }
                    },
                    "next": {
                      "block": {
                        "type": "tactic_other",
                        "id": "example3-tactic",
                        "fields": { "PROP_NAME": "ring" }
                      }
                    }
                  }
                }
              }
            }
          }
        }]
      }
    }
  },
  {
    name: "Field 𝕜",
    initial: {
      "blocks": {
        "languageVersion": 0,
        "blocks": [{
          "type": "lemma",
          "id": "test-lemma",
          "x": 20,
          "y": 20,
          "fields": {
            "THEOREM_NAME": "test",
            "THEOREM_DECLARATION": ": 𝕜 = 𝕜"
          },
          "inputs": {
            "LEMMA_PROOF": {
              "block": {
                "type": "tactic_other",
                "id": "test-tactic",
                "fields": { "PROP_NAME": "rfl" }
              }
            }
          }
        }]
      }
    }
  }
];

// CSS
import './css/App.css'
import './css/Editor.css'

/** Returns true if the browser wants dark mode */
function isBrowserDefaultDark() {
  return window.matchMedia('(prefers-color-scheme: dark)').matches
}

function Wrapp(props: {
  editor: monaco.editor.IStandaloneCodeEditor,
  setEditor: (e: monaco.editor.IStandaloneCodeEditor) => void,
}) {
  const { editor, setEditor } = props;
  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [loaded, setLoaded] = useState<boolean>(false)
  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)
  const { width } = useWindowDimensions()


  // Lean4monaco options
  const [options, setOptions] = useState<LeanMonacoOptions>({
    // placeholder, updated below
    websocket: { url: '' }
  })

  // Because of Monaco's missing mobile support we add a codeMirror editor
  // which can be enabled to do editing.
  // TODO: It would be nice to integrate Lean into CodeMirror better.
  // first step could be to pass the cursor selection to the underlying monaco editor
  const [codeMirror, setCodeMirror] = useState(false)

  // the user data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>(undefined)
  const [url, setUrl] = useState<string | null>(null)
  const [codeFromUrl, setCodeFromUrl] = useState<string>('')

  /** Monaco editor requires the code to be set manually. */
  function setContent(code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  // Read the URL arguments
  useEffect(() => {
    // Parse args
    console.log('[Lean4web] Parsing URL')
    let args = parseArgs()
    if (args.code) {
      let _code = decodeURIComponent(args.code)
      setContent(_code)
    } else if (args.codez) {
      let _code = LZString.decompressFromBase64(args.codez)
      setContent(_code)
    }

    if (args.url) { setUrl(lookupUrl(decodeURIComponent(args.url))) }

    // if no project provided, use default
    let project = args.project || 'MathlibDemo'

    console.log(`[Lean4web] Setting project to ${project}`)
    setProject(project)
  }, [])

  // Load preferences from store in the beginning
  useEffect(() => {
    // only load them once
    if (loaded) { return }
    console.debug('[Lean4web] Loading preferences')

    let saveInLocalStore = false;
    let newPreferences: { [K in keyof IPreferencesContext]: IPreferencesContext[K] } = { ...preferences }
    for (const [key, value] of (Object.entries(preferences) as Entries<IPreferencesContext>)) {
      // prefer URL params over stored
      const searchParams = new URLSearchParams(window.location.search);
      let storedValue = (
        preferenceParams.includes(key) &&  // only for keys we explictly check for
        searchParams.has(key) && searchParams.get(key))
        ?? window.localStorage.getItem(key)
      if (storedValue) {
        saveInLocalStore = window.localStorage.getItem(key) === storedValue
        console.debug(`[Lean4web] Found value for ${key}: ${storedValue}`)
        if (typeof value === 'string') {
          if (key == 'theme') {
            const theme = storedValue.toLowerCase().includes('dark') ? "Visual Studio Dark" : "Visual Studio Light"
            newPreferences[key] = theme
          }
          else {
            newPreferences[key] = storedValue
          }
        } else if (typeof value === 'boolean') {
          newPreferences[key] = (storedValue === "true")
        } else {
          // other values aren't implemented yet.
          console.error(`[Lean4web] Preferences (key: ${key}) contain a value of unsupported type: ${typeof value}`)
        }
      } else {
        // no stored preferences, set a default value
        if (key == 'theme') {
          if (isBrowserDefaultDark()) {
            console.debug("[Lean4web] Preferences: Set dark theme.")
            newPreferences['theme'] = 'Visual Studio Dark'
          } else {
            console.debug("[Lean4web] Preferences: Set light theme.")
            newPreferences['theme'] = 'Visual Studio Light'
          }
        }
      }
    }
    newPreferences['saveInLocalStore'] = saveInLocalStore
    setPreferences(newPreferences)
    setLoaded(true)
  }, [])

  // Use the window width to switch between mobile/desktop layout
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    const _mobile = width < 800
    const searchParams = new URLSearchParams(window.location.search);
    if (!(searchParams.has("mobile") || preferences.saveInLocalStore) && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width, loaded])

  // Update LeanMonaco options when preferences are loaded or change
  useEffect(() => {
    if (!project) { return }
    console.log('[Lean4web] Update lean4monaco options')

    var socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") +
      window.location.host + "/websocket/" + project
    console.log(`[Lean4web] Socket url is ${socketUrl}`)
    var _options: LeanMonacoOptions = {
      websocket: { url: socketUrl },
      // Restrict monaco's extend (e.g. context menu) to the editor itself
      htmlElement: editorRef.current ?? undefined,
      vscode: {
        /* To add settings here, you can open your settings in VSCode (Ctrl+,), search
         * for the desired setting, select "Copy Setting as JSON" from the "More Actions"
         * menu next to the selected setting, and paste the copied string here.
         */
        "workbench.colorTheme": preferences.theme,
        "editor.tabSize": 2,
        // "editor.rulers": [100],
        "editor.lightbulb.enabled": "on",
        "editor.wordWrap": preferences.wordWrap ? "on" : "off",
        "editor.wrappingStrategy": "advanced",
        "editor.semanticHighlighting.enabled": true,
        "editor.acceptSuggestionOnEnter": preferences.acceptSuggestionOnEnter ? "on" : "off",
        "lean4.input.eagerReplacementEnabled": true,
        "lean4.infoview.showGoalNames": preferences.showGoalNames,
        "lean4.infoview.emphasizeFirstGoal": true,
        "lean4.infoview.showExpectedType": false,
        "lean4.infoview.showTooltipOnHover": false,
        "lean4.input.leader": preferences.abbreviationCharacter
      }
    }
    setOptions(_options)
  }, [editorRef, project, preferences])

  // Setting up the editor and infoview
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }
    console.debug('[Lean4web] Restarting editor')
    var _leanMonaco = new LeanMonaco()
    var leanMonacoEditor = new LeanMonacoEditor()

    _leanMonaco.setInfoviewElement(infoviewRef.current!)
      ; (async () => {
        await _leanMonaco.start(options)
        await leanMonacoEditor.start(editorRef.current!, path.join(project, `${project}.lean`), code)

        setEditor(leanMonacoEditor.editor)
        setLeanMonaco(_leanMonaco)

        // Add a `Paste` option to the context menu on mobile.
        // Monaco does not support clipboard pasting as all browsers block it
        // due to security reasons. Therefore we use a codeMirror editor overlay
        // which features good mobile support (but no Lean support yet)
        if (preferences.mobile) {
          leanMonacoEditor.editor?.addAction({
            id: "myPaste",
            label: "Paste: open 'Plain Editor' for editing on mobile",
            // keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KEY_V],
            contextMenuGroupId: "9_cutcopypaste",
            run: (_editor) => {
              setCodeMirror(true)
            }
          })
        }

        // // TODO: This was an approach to create a new definition provider, but it
        // // wasn't that useful. I'll leave it here in connection with the TODO below for
        // // reference.
        // monaco.languages.registerDefinitionProvider('lean4', {
        //   provideDefinition(model, position) {
        //     const word = model.getWordAtPosition(position);
        //     if (word) {
        //       console.log(`[Lean4web] Providing definition for: ${word.word}`);
        //       // Return the location of the definition
        //       return [
        //         {
        //           uri: model.uri,
        //           range: {startLineNumber: 0, startColumn: word.startColumn, endColumn: word.endColumn, endLineNumber: 0}, // Replace with actual definition range
        //         },
        //       ];
        //     }
        //     return null;
        //   },
        // });

        // TODO: Implement Go-To-Definition better
        // This approach only gives us the file on the server (plus line number) it wants
        // to open, is there a better approach?
        const editorService = (leanMonacoEditor.editor as any)?._codeEditorService
        if (editorService) {
          const openEditorBase = editorService.openCodeEditor.bind(editorService)
          editorService.openCodeEditor = async (input: any, source: any) => {
            const result = await openEditorBase(input, source)
            if (result === null) {
              // found this out with `console.debug(input)`:
              // `resource.path` is the file go-to-def tries to open on the disk
              // we try to create a doc-gen link from that. Could not extract the
              // (fully-qualified) decalaration name... with that one could
              // call `...${path}.html#${declaration}`
              let path = input.resource.path.replace(
                new RegExp("^.*/(?:lean|\.lake/packages/[^/]+/)"), ""
              ).replace(
                new RegExp("\.lean$"), ""
              )

              if (window.confirm(`Do you want to open the docs?\n\n${path} (line ${input.options.selection.startLineNumber})`)) {
                let newTab = window.open(`https://leanprover-community.github.io/mathlib4_docs/${path}.html`, "_blank")
                if (newTab) {
                  newTab.focus()
                }
              }
            }
            return null
            // return result // always return the base result
          }
        }

        // Keeping the `code` state up-to-date with the changes in the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
      })()
    return () => {
      leanMonacoEditor.dispose()
      _leanMonaco.dispose()
    }
  }, [loaded, project, preferences, options, infoviewRef, editorRef])

  // Load content from source URL.
  // Once the editor is loaded, this reads the content of any provided `url=` in the URL and
  // saves this content as `codeFromURL`. It is important that we only do this once
  // the editor is loaded, as the `useEffect` below only triggers when the `codeFromURL`
  // changes, otherwise it might overwrite local changes too often.
  useEffect(() => {
    if (!editor || !url) { return }
    console.debug(`[Lean4web] Loading from ${url}`)
    fetch(url)
      .then((response) => response.text())
      .then((code) => {
        setCodeFromUrl(code)
      })
      .catch(err => {
        let errorTxt = `ERROR: ${err.toString()}`
        console.error(errorTxt)
        setCodeFromUrl(errorTxt)
      })
  }, [url, editor])

  // Sets the editors content to the content from the loaded URL.
  // As described above, this requires the editor is loaded, but we do not want to
  // trigger this effect every time the editor is reloaded (e.g. config change) as otherwise
  // we would constantly overwrite the user's local changes
  useEffect(() => {
    if (!codeFromUrl) { return }
    setContent(codeFromUrl)
  }, [codeFromUrl])

  // Keep the URL updated on change
  useEffect(() => {
    if (!editor) { return }

    let _project = (project == 'MathlibDemo' ? null : project)
    let args: {
      project: string | null
      url: string | null
      code: string | null
      codez: string | null
    }
    if (code === "") {
      args = {
        project: _project,
        url: null,
        code: null,
        codez: null
      }
    } else if (url != null && code == codeFromUrl) {
      args = {
        project: _project,
        url: encodeURIComponent(url),
        code: null,
        codez: null
      }
    } else if (preferences.compress) {
      // LZ padds the string with trailing `=`, which mess up the argument parsing
      // and aren't needed for LZ encoding, so we remove them.
      const compressed = LZString.compressToBase64(code).replace(/=*$/, '')
      // // Note: probably temporary; might be worth to always compress as with whitespace encoding
      // // it needs very little for the compressed version to be shorter
      // const encodedCode = fixedEncodeURIComponent(code)
      // console.debug(`[Lean4web] Code length: ${encodedCode.length}, compressed: ${compressed.length}`)
      // if (compressed.length < encodedCode.length) {
      args = {
        project: _project,
        url: null,
        code: null,
        codez: compressed
      }
      // } else {
      //   args = {
      //     project: _project,
      //     url: null,
      //     code: encodedCode,
      //     codez: null
      //   }
      // }
    } else {
      args = {
        project: _project,
        url: null,
        code: fixedEncodeURIComponent(code),
        codez: null
      }
    }
    history.replaceState(undefined, undefined!, formatArgs(args))
  }, [editor, project, code, codeFromUrl])

  // Disable monaco context menu outside the editor
  useEffect(() => {
    const handleContextMenu = (event: MouseEvent) => {
      const editorContainer = document.querySelector(".editor")
      // Always prevent default context menu
      event.preventDefault();
      if (editorContainer && !editorContainer.contains(event.target as Node)) {
        event.stopPropagation();
      }
    }
    document.addEventListener("contextmenu", handleContextMenu, true)
    return () => {
      document.removeEventListener("contextmenu", handleContextMenu, true)
    }
  }, [])

  // Stop the browser's save dialog on Ctrl+S
  const handleKeyDown = useCallback((event: KeyboardEvent) => {
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 's') {
      event.preventDefault()
    }
  }, [])

  // Actually save the file on Ctrl+S
  const handleKeyUp = useCallback((event: KeyboardEvent) => {
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 's') {
      event.preventDefault()
      save(code)
    }
  }, [code])

  useEffect(() => {
    document.addEventListener('keydown', handleKeyDown)
    document.addEventListener('keyup', handleKeyUp)
    return () => {
      document.removeEventListener('keydown', handleKeyDown)
      document.removeEventListener('keyup', handleKeyUp)
    }
  }, [handleKeyDown, handleKeyUp])

  return <PreferencesContext.Provider value={{ preferences, setPreferences }}>
    <div className="app monaco-editor">
      <nav>
        <LeanLogo />
        <Menu
          code={code}
          setContent={setContent}
          project={project}
          setProject={setProject}
          setUrl={setUrl}
          codeFromUrl={codeFromUrl}
          restart={leanMonaco?.restart}
          codeMirror={codeMirror}
          setCodeMirror={setCodeMirror}
        />
      </nav>
      <Split className={`editor ${dragging ? 'dragging' : ''}`}
        gutter={(_index, _direction) => {
          const gutter = document.createElement('div')
          gutter.className = `gutter` // no `gutter-${direction}` as it might change
          return gutter
        }}
        gutterStyle={(_dimension, gutterSize, _index) => {
          return {
            'width': preferences.mobile ? '100%' : `${gutterSize}px`,
            'height': preferences.mobile ? `${gutterSize}px` : '100%',
            'cursor': preferences.mobile ? 'row-resize' : 'col-resize',
            'margin-left': preferences.mobile ? 0 : `-${gutterSize}px`,
            'margin-top': preferences.mobile ? `-${gutterSize}px` : 0,
            'z-index': 0,
          }
        }}
        gutterSize={5}
        onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}
        sizes={preferences.mobile ? [50, 50] : [70, 30]}
        direction={preferences.mobile ? "vertical" : "horizontal"}
        style={{ flexDirection: preferences.mobile ? "column" : "row" }}>
        <div className='codeview-wrapper'
          style={preferences.mobile ? { width: '100%' } : { height: '100%' }} >
          {codeMirror &&
            <CodeMirror
              className="codeview plain"
              value={code}
              extensions={[EditorView.lineWrapping]}
              height='100%'
              maxHeight='100%'
              theme={lightThemes.includes(preferences.theme) ? 'light' : 'dark'}
              onChange={setContent} />
          }
          <div ref={editorRef} className={`codeview${codeMirror ? ' hidden' : ''}`} />
        </div>
        <div ref={infoviewRef} className="vscode-light infoview"
          style={preferences.mobile ? { width: '100%' } : { height: '100%' }} >
          <p className={`editor-support-warning${codeMirror ? '' : ' hidden'}`} >
            You are in the plain text editor<br /><br />
            Go back to the Monaco Editor (click <FontAwesomeIcon icon={faCode} />)
            for the infoview to update!
          </p>
        </div>
      </Split>
    </div>
  </PreferencesContext.Provider>

}

// Virtual document URI for Blockly code (must match what RpcSessionManager uses)
const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';

function App() {
  const [show, setShow] = useState(true);
  const [goals, setGoals] = useState<InteractiveGoals | null>(null);
  const [goalsLoading, setGoalsLoading] = useState(false);
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const blocklyRef = useRef<BlocklyHandle>(null);
  const [currentLevelIndex, setCurrentLevelIndex] = useState(0);
  const [levelStates, setLevelStates] = useState<BlocklyState[]>(
    () => levelDefinitions.map(ex => ex.initial)
  );

  // RPC session manager for Blockly code
  const rpcManagerRef = useRef<RpcSessionManager | null>(null);
  const [rpcManagerReady, setRpcManagerReady] = useState(false);

  // Initialize RPC session manager when editor is ready (Lean client available)
  useEffect(() => {
    if (!editor) return;

    // Create manager if not exists
    if (!rpcManagerRef.current) {
      rpcManagerRef.current = new RpcSessionManager(BLOCKLY_DOC_URI);
    }

    // Try to initialize (may need to retry if Lean client not ready yet)
    const initManager = async () => {
      const success = await rpcManagerRef.current!.initialize();
      if (success) {
        console.log('[App] RpcSessionManager initialized');
        setRpcManagerReady(true);
      } else {
        // Retry after a delay - Lean client may not be ready yet
        console.log('[App] RpcSessionManager init failed, retrying in 1s...');
        setTimeout(initManager, 1000);
      }
    };

    initManager();

    return () => {
      rpcManagerRef.current?.dispose();
      rpcManagerRef.current = null;
      setRpcManagerReady(false);
    };
  }, [editor]);

  function switchToLevel(newIndex: number) {
    if (newIndex === currentLevelIndex) return;

    // Save current workspace state
    const currentState = blocklyRef.current?.saveWorkspace();
    if (currentState) {
      setLevelStates(prev => {
        const updated = [...prev];
        updated[currentLevelIndex] = currentState;
        return updated;
      });
    }

    // Load the new level
    blocklyRef.current?.loadWorkspace(levelStates[newIndex]);
    setCurrentLevelIndex(newIndex);
  }

  function resetCurrentLevel() {
    const initialState = levelDefinitions[currentLevelIndex].initial;
    blocklyRef.current?.loadWorkspace(initialState);
    setLevelStates(prev => {
      const updated = [...prev];
      updated[currentLevelIndex] = initialState;
      return updated;
    });
  }

  function injectClick(s: string, p: monaco.IPosition) {
    const model = editor.getModel();
    model.setValue(s);
    editor.setPosition(p);
    // editor.focus();
  }

  function focusClick() {
    editor.focus();
  }

  const [dragging, setDragging] = useState(false);

  const myStyle: React.CSSProperties = {
    position: 'absolute',
    top: 0, left: 0, right: 0, bottom: 0,
    overflow: 'hidden',
  };
  const kid1: React.CSSProperties = {
    display: 'flex',
    flexDirection: 'row',
    overflow: 'hidden',
  };
  const blocklyContainer: React.CSSProperties = {
    flexGrow: 1,
  };
  function changeChecked(e: React.ChangeEvent) {
    setShow((e.currentTarget as HTMLInputElement).checked);
  }
  function onBlocklyChange(result: WorkspaceToLeanResult) {
    const { leanCode, sourceInfo } = result;
    const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

`;
    const fullCode = prelude + leanCode;

    // Update Monaco editor (for debugging/viewing)
    editor.getModel().setValue(fullCode);


    // Independently fetch goals from Lean server
    // (async () => {
    //   try {
    //     // Get goals at the sorry position (line 2, char 2 - where "sorry" starts)
    //     const goals = await getGoalsForCode(testCode, 2, 2);
    //     if (goals) {
    //       console.log('[onBlocklyChange] Received goals:', goals);

    //     } else {
    //       console.log('[onBlocklyChange] No goals received');
    //     }
    //   } catch (err) {
    //     console.error('[onBlocklyChange] Error fetching goals:', err);
    //   }
    // })();
  }

  const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

`;

  async function onRequestGoals(
    blockId: string,
    leanCode: string,
    sourceInfo: SourceInfo[],
    blockSourceInfo: SourceInfo | undefined
  ) {
    console.log('[onRequestGoals] ========================================');
    console.log('[onRequestGoals] Block ID:', blockId);
    console.log('[onRequestGoals] Block source info:', blockSourceInfo);

    if (!blockSourceInfo) {
      console.log('[onRequestGoals] No source info for block, cannot fetch goals');
      return;
    }

    if (!rpcManagerRef.current) {
      console.log('[onRequestGoals] RPC manager not initialized');
      return;
    }

    // Use the start position of the block to query for goals
    const [line, col] = blockSourceInfo.startLineCol;

    // Account for the prelude offset
    const preludeLines = prelude.split('\n').length - 1; // -1 because split gives one more
    const adjustedLine = line + preludeLines;

    const fullCode = prelude + leanCode;

    console.log('[onRequestGoals] Prelude lines:', preludeLines);
    console.log('[onRequestGoals] Original position: line', line, 'col', col);
    console.log('[onRequestGoals] Adjusted position: line', adjustedLine, 'col', col);
    console.log('[onRequestGoals] Full code being sent:');
    console.log('---BEGIN CODE---');
    console.log(fullCode);
    console.log('---END CODE---');

    // Show the specific line we're querying
    const codeLines = fullCode.split('\n');
    if (adjustedLine < codeLines.length) {
      console.log('[onRequestGoals] Line at query position:', JSON.stringify(codeLines[adjustedLine]));
      console.log('[onRequestGoals] Character at position:', JSON.stringify(codeLines[adjustedLine]?.[col]));
    }

    setGoalsLoading(true);
    try {
      console.log('[onRequestGoals] Fetching goals via RpcSessionManager...');
      const goals = await rpcManagerRef.current.getGoals(fullCode, adjustedLine, col);
      console.log('[onRequestGoals] Goals received:', goals);

      if (goals) {
        console.log('[onRequestGoals] Setting goals');
        setGoals(goals);
      } else {
        console.log('[onRequestGoals] No goals returned');
      }
    } catch (err) {
      console.error('[onRequestGoals] Error fetching goals:', err);
    } finally {
      setGoalsLoading(false);
    }
  }

  return <div style={myStyle}>
    <Split
      className={dragging ? 'dragging' : ''}
      direction="vertical"
      sizes={[60, 40]}
      minSize={100}
      gutterSize={5}
      onDragStart={() => setDragging(true)}
      onDragEnd={() => setDragging(false)}
      style={{ display: 'flex', flexDirection: 'column', height: '100%' }}
      gutter={() => {
        const gutter = document.createElement('div');
        gutter.className = 'gutter gutter-vertical';
        return gutter;
      }}
      gutterStyle={() => ({
        height: '5px',
        backgroundColor: '#ccc',
      })}
    >
      <div style={kid1}>
        <div className="buttons">
          {levelDefinitions.map((ex, i) => (
            <button
              key={i}
              onClick={() => switchToLevel(i)}
              style={{ fontWeight: i === currentLevelIndex ? 'bold' : 'normal' }}
            >
              {i + 1}
            </button>
          ))}
          <button onClick={resetCurrentLevel}>Reset</button>
          <button onClick={() => {
            const state = blocklyRef.current?.saveWorkspace();
            if (state) {
              navigator.clipboard.writeText(JSON.stringify(state, null, 2));
              console.log('Workspace copied to clipboard');
            }
          }}>Copy</button>
        </div>
        <Blockly ref={blocklyRef} style={blocklyContainer} onBlocklyChange={onBlocklyChange} onRequestGoals={onRequestGoals} initialData={levelDefinitions[0].initial} />
        <div style={{ width: '300px', padding: '0.5em', borderLeft: '1px solid #ccc', overflow: 'auto' }}>
          {goalsLoading ? (
            <div className="goals-loading">
              <div className="spinner" />
              <span>Loading goals...</span>
            </div>
          ) : (
            <Goals goals={goals} />
          )}
        </div>
      </div>
      <div style={{ overflow: 'hidden' }}>{show ? <Wrapp editor={editor} setEditor={setEditor} /> : undefined}</div>
    </Split>
  </div>;
}

/* var selection = editor.getSelection();
 * var id = { major: 1, minor: 1 };
 * var text = "XXX";
 * var op = {identifier: id, range: selection, text: text, forceMoveMarkers: true};
 * editor.executeEdits("my-source", [op]); */
export default App

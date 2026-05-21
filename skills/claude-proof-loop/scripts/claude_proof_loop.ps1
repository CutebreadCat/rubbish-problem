param(
    [Parameter(Mandatory = $true)]
    [string]$ProblemDir,

    [Parameter(Mandatory = $true)]
    [string]$Target,

    [string]$LeanFile = "",
    [string]$LeanCheckCommand = "",
    [int]$MaxIterations = 1,
    [string]$ClaudeCommand = "claude",
    [string[]]$ClaudeArgs = @("-p"),
    [int]$ClaudeTimeoutSeconds = 120,
    [switch]$Continuous,
    [switch]$AutoGit,
    [switch]$Push,
    [string]$CommitMessage = "Update proof loop materials"
)

$ErrorActionPreference = "Stop"

$root = (Resolve-Path ".").Path
$problemPath = (Resolve-Path $ProblemDir).Path
if (-not $problemPath.StartsWith($root, [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "ProblemDir must stay inside the current repository."
}

$logDir = Join-Path $problemPath "proof-log"
New-Item -ItemType Directory -Force -Path $logDir | Out-Null

$sourceSummary = Join-Path $problemPath "materials\source-summary.md"
$researchDirections = Join-Path $problemPath "materials\research-directions.md"

$contextParts = @()
if (Test-Path $sourceSummary) {
    $contextParts += "SOURCE SUMMARY:`n$(Get-Content -Raw $sourceSummary)"
}
if (Test-Path $researchDirections) {
    $contextParts += "RESEARCH DIRECTIONS:`n$(Get-Content -Raw $researchDirections)"
}
$context = $contextParts -join "`n`n---`n`n"

$claudeAvailable = $false
try {
    $null = Get-Command $ClaudeCommand -ErrorAction Stop
    $claudeAvailable = $true
} catch {
    $claudeAvailable = $false
}

$iterationLimit = $MaxIterations
if ($Continuous) {
    if (-not $claudeAvailable) {
        throw "Continuous mode requires a Claude CLI command. Install/configure Claude or run with a finite MaxIterations to generate manual prompts."
    }
    $iterationLimit = [int]::MaxValue
}

$previousReview = ""

function Invoke-ClaudeText {
    param(
        [string]$Command,
        [string[]]$Arguments,
        [string]$PromptText,
        [int]$TimeoutSeconds
    )

    $job = Start-Job -ScriptBlock {
        param($cmd, $argsForCmd, $text)
        & $cmd @argsForCmd $text
    } -ArgumentList $Command, $Arguments, $PromptText

    if (Wait-Job $job -Timeout $TimeoutSeconds) {
        return (Receive-Job $job)
    }

    Stop-Job $job | Out-Null
    Remove-Job $job | Out-Null
    throw "Claude call timed out after $TimeoutSeconds seconds."
}

for ($i = 1; $i -le $iterationLimit; $i++) {
    $stamp = "{0:000}" -f $i
    $promptPath = Join-Path $logDir "iteration-$stamp-prompt.md"
    $attemptPath = Join-Path $logDir "iteration-$stamp-attempt.md"
    $reviewPath = Join-Path $logDir "iteration-$stamp-review.md"
    $leanOutputPath = Join-Path $logDir "iteration-$stamp-lean-output.txt"
    if ($LeanFile) {
        $currentLeanPath = $LeanFile
    } else {
        $currentLeanPath = Join-Path $logDir "iteration-$stamp.lean"
    }

    $prompt = @"
You are working on a hard mathematical problem through Lean formalization. Do not claim a full solution unless Lean checks the exact theorem without placeholders.

Target for this iteration:
$Target

Lean file to create or update:
$currentLeanPath

Local context:
$context

Previous review notes:
$previousReview

Produce:
1. A precise Lean theorem or lemma statement.
2. A Lean proof attempt as the first fenced code block.
3. Any imports required.
4. A list of all floor, parity, endpoint, and large-n obligations.
5. The weakest formalization step.
6. A suggested narrower Lean target if the proof fails.
"@

    Set-Content -LiteralPath $promptPath -Value $prompt -Encoding UTF8

    if ($claudeAvailable) {
        try {
            $attempt = Invoke-ClaudeText -Command $ClaudeCommand -Arguments $ClaudeArgs -PromptText $prompt -TimeoutSeconds $ClaudeTimeoutSeconds
            if (-not ($attempt -join "`n").Trim()) {
                throw "Claude returned empty output."
            }
            $attemptText = $attempt -join "`n"
            Set-Content -LiteralPath $attemptPath -Value $attemptText -Encoding UTF8
        } catch {
            Set-Content -LiteralPath $attemptPath -Value "Claude call failed: $($_.Exception.Message)" -Encoding UTF8
            Set-Content -LiteralPath $reviewPath -Value "Pending; attempt generation failed or timed out." -Encoding UTF8
            $previousReview = "Attempt generation failed or timed out."
            break
        }

        if (-not (Test-Path $currentLeanPath)) {
            Set-Content -LiteralPath $currentLeanPath -Value "-- Paste or extract the Lean code block from iteration-$stamp-attempt.md here, then rerun the loop." -Encoding UTF8
        }

        $leanOutput = ""
        if ($LeanCheckCommand) {
            try {
                $leanOutput = Invoke-Expression "$LeanCheckCommand `"$currentLeanPath`"" 2>&1 | Out-String
            } catch {
                $leanOutput = $_ | Out-String
            }
        } elseif ((Test-Path "lakefile.lean") -or (Test-Path "lakefile.toml") -or (Test-Path "lake-manifest.json")) {
            try {
                $leanOutput = lake env lean $currentLeanPath 2>&1 | Out-String
            } catch {
                $leanOutput = $_ | Out-String
            }
        } elseif (Get-Command lean -ErrorAction SilentlyContinue) {
            try {
                $leanOutput = lean $currentLeanPath 2>&1 | Out-String
            } catch {
                $leanOutput = $_ | Out-String
            }
        } else {
            $leanOutput = "Lean toolchain not found."
        }
        Set-Content -LiteralPath $leanOutputPath -Value $leanOutput -Encoding UTF8

        $reviewPrompt = @"
Review the following Lean formalization attempt adversarially. Use the Lean output as primary evidence. Look for false claims, missing cases, endpoint failures, hidden assumptions, placeholders, and counterexamples. Give verdict pass, revise, or reject.

Problem context:
$context

Attempt:
$(Get-Content -Raw $attemptPath)

Lean output:
$(Get-Content -Raw $leanOutputPath)
"@
        try {
            $review = Invoke-ClaudeText -Command $ClaudeCommand -Arguments $ClaudeArgs -PromptText $reviewPrompt -TimeoutSeconds $ClaudeTimeoutSeconds
            $reviewText = $review -join "`n"
            if (-not $reviewText.Trim()) {
                $reviewText = "Claude review returned empty output."
            }
        } catch {
            $reviewText = "Claude review failed: $($_.Exception.Message)"
        }
        Set-Content -LiteralPath $reviewPath -Value $reviewText -Encoding UTF8
        $previousReview = $reviewText
        if ($reviewText -match "(?im)^\s*verdict\s*:\s*pass\s*$") {
            Write-Host "Review verdict is pass; stopping loop."
            break
        }
    } else {
        Set-Content -LiteralPath $attemptPath -Value "Claude CLI not found. Paste iteration-$stamp-prompt.md into Claude and save the response here." -Encoding UTF8
        Set-Content -LiteralPath $reviewPath -Value "Pending. After saving the attempt, ask Claude or another reviewer to perform adversarial review." -Encoding UTF8
        $previousReview = "No automated review; Claude CLI not found."
    }
}

if ($AutoGit) {
    git status --short
    git add -- $ProblemDir "skills/claude-proof-loop"
    $pending = git diff --cached --name-only
    if ($pending) {
        git commit -m $CommitMessage
        if ($Push) {
            git push
        }
    } else {
        Write-Host "No staged changes to commit."
    }
}

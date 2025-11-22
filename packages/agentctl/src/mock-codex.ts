import fs from 'fs';
import path from 'path';
import { setTimeout } from 'timers/promises';

async function main() {
    // Parse args minimally to find --output-final-message and the instruction file
    const args = process.argv.slice(2);
    const outputFinalMessageIndex = args.indexOf('--output-final-message');
    let finalMessagePath: string | null = null;

    if (outputFinalMessageIndex !== -1 && args.length > outputFinalMessageIndex + 1) {
        finalMessagePath = args[outputFinalMessageIndex + 1];
    }

    const instructionFile = process.env.AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE;
    if (!instructionFile) {
        console.error('Error: AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE not set');
        process.exit(1);
    }

    if (!fs.existsSync(instructionFile)) {
        console.error(`Error: Instruction file not found: ${instructionFile}`);
        process.exit(1);
    }

    const content = fs.readFileSync(instructionFile, 'utf-8');
    const lines = content.split('\n').filter(line => line.trim() !== '');

    for (const line of lines) {
        try {
            const event = JSON.parse(line);

            // Simulate delay if specified in the mock event (custom field)
            if (event._mock_delay_ms) {
                await setTimeout(event._mock_delay_ms);
                delete event._mock_delay_ms; // Remove before printing
            }

            // Simulate crash/exit
            if (event._mock_exit_code !== undefined) {
                process.exit(event._mock_exit_code);
            }

            console.log(JSON.stringify(event));

            // If this is a final message event, write to file if requested
            // Assuming the event structure has 'finalMessage' or similar. 
            // For the mock, we'll assume the last event might contain the final message text
            // or we explicitly look for a 'final_message' field in the event.
            if (finalMessagePath && event.type === 'turn_end' && event.final_message) {
                fs.writeFileSync(finalMessagePath, event.final_message);
            }

        } catch (e) {
            console.error('Failed to parse mock line:', line);
        }
    }
}

main().catch(err => {
    console.error(err);
    process.exit(1);
});
